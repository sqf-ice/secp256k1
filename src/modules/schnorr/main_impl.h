/**********************************************************************
 * Copyright (c) 2014-2015 Pieter Wuille                              *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_MODULE_SCHNORR_MAIN
#define SECP256K1_MODULE_SCHNORR_MAIN

#include "include/secp256k1_schnorr.h"
#include "modules/schnorr/schnorr_impl.h"

static void secp256k1_schnorr_msghash_sha256(unsigned char *h32, const unsigned char *r32, const unsigned char *msg32) {
    secp256k1_sha256_t sha;
    secp256k1_sha256_initialize(&sha);
    secp256k1_sha256_write(&sha, r32, 32);
    secp256k1_sha256_write(&sha, msg32, 32);
    secp256k1_sha256_finalize(&sha, h32);
}

static const unsigned char secp256k1_schnorr_algo16[17] = "Schnorr+SHA256  ";

int secp256k1_schnorr_sign(const secp256k1_context* ctx, unsigned char *sig64, const unsigned char *msg32, const unsigned char *seckey, secp256k1_nonce_function noncefp, const void *ndata) {
    secp256k1_scalar sec, nonce_mine;
    secp256k1_ge pubnonce_all;
    int ret = 0;
    int overflow = 0;
    unsigned int count = 0;
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(sig64 != NULL);
    ARG_CHECK(seckey != NULL);
    if (noncefp == NULL) {
        noncefp = secp256k1_nonce_function_default;
    }

    secp256k1_scalar_set_b32(&sec, seckey, &overflow);
    ret = !secp256k1_scalar_is_zero(&sec) && !overflow;
    while (ret) {
        unsigned char nonce32[32];
        ret = noncefp(nonce32, msg32, seckey, secp256k1_schnorr_algo16, (void*)ndata, count);
        if (!ret) {
            break;
        }
        ret = secp256k1_schnorr_nonces_set_b32(&ctx->ecmult_gen_ctx, &nonce_mine, &pubnonce_all, nonce32, NULL) &&
            secp256k1_schnorr_sig_sign(sig64, &sec, &nonce_mine, &pubnonce_all, secp256k1_schnorr_msghash_sha256, msg32);
        memset(nonce32, 0, 32);
        if (ret) {
            break;
        }
        count++;
    }
    if (!ret) {
        memset(sig64, 0, 64);
    }
    secp256k1_scalar_clear(&nonce_mine);
    secp256k1_scalar_clear(&sec);
    return ret;
}

int secp256k1_schnorr_verify(const secp256k1_context* ctx, const unsigned char *sig64, const unsigned char *msg32, const secp256k1_pubkey *pubkey) {
    secp256k1_ge q;
    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(sig64 != NULL);
    ARG_CHECK(pubkey != NULL);

    secp256k1_pubkey_load(ctx, &q, pubkey);
    return secp256k1_schnorr_sig_verify(&ctx->ecmult_ctx, sig64, &q, secp256k1_schnorr_msghash_sha256, msg32);
}

int secp256k1_schnorr_recover(const secp256k1_context* ctx, secp256k1_pubkey *pubkey, const unsigned char *sig64, const unsigned char *msg32) {
    secp256k1_ge q;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(sig64 != NULL);
    ARG_CHECK(pubkey != NULL);

    if (secp256k1_schnorr_sig_recover(&ctx->ecmult_ctx, sig64, &q, secp256k1_schnorr_msghash_sha256, msg32)) {
        secp256k1_pubkey_save(pubkey, &q);
        return 1;
    } else {
        memset(pubkey, 0, sizeof(*pubkey));
        return 0;
    }
}

static int secp256k1_multischnorr_compute_tweak(secp256k1_scalar* tweak, const secp256k1_ge* pubkey) {
    secp256k1_ge ge = *pubkey;
    unsigned char c[33];
    unsigned char h[32];
    size_t size = 33;
    secp256k1_sha256_t sha;
    int overflow = 0;

    if (!secp256k1_eckey_pubkey_serialize(&ge, c, &size, SECP256K1_EC_COMPRESSED)) {
        return 0;
    }
    secp256k1_sha256_initialize(&sha);
    secp256k1_sha256_write(&sha, c, size);
    secp256k1_sha256_finalize(&sha, h);
    secp256k1_scalar_set_b32(tweak, h, &overflow);
    if (overflow || secp256k1_scalar_is_zero(tweak)) {
        secp256k1_scalar_clear(tweak);
        return 0;
    }
    return 1;
}

static int secp256k1_multischnorr_compute_tweaked_privkey(const secp256k1_context* ctx, secp256k1_scalar* key, unsigned char *sec32out, const unsigned char *sec32in) {
    secp256k1_gej pubj;
    secp256k1_ge pub;
    secp256k1_scalar tweak;
    int overflow = 0;
    int ret;

    secp256k1_scalar_set_b32(key, sec32in, &overflow);
    ret = !overflow && !secp256k1_scalar_is_zero(key);
    if (ret) {
        secp256k1_ecmult_gen(&ctx->ecmult_gen_ctx, &pubj, key);
        secp256k1_ge_set_gej(&pub, &pubj);
        ret = secp256k1_multischnorr_compute_tweak(&tweak, &pub);
    }
    if (ret) {
        secp256k1_scalar_mul(key, key, &tweak);
        secp256k1_scalar_get_b32(sec32out, key);
    } else {
        secp256k1_scalar_clear(key);
        memset(sec32out, 0, 32);
    }
    return ret;
}

static int secp256k1_multischnorr_compute_tweaked_pubkey(const secp256k1_context* ctx, secp256k1_gej* pub_tweaked, const secp256k1_ge* pub) {
    secp256k1_scalar tweak;
    static const secp256k1_scalar zero = SECP256K1_SCALAR_CONST(0, 0, 0, 0, 0, 0, 0, 0);
    int ret;

    ret = secp256k1_multischnorr_compute_tweak(&tweak, pub);
    if (ret) {
        secp256k1_gej_set_ge(pub_tweaked, pub);
        secp256k1_ecmult(&ctx->ecmult_ctx, pub_tweaked, pub_tweaked, &tweak, &zero);
    }
    if (!ret) {
        secp256k1_gej_clear(pub_tweaked);
    }
    return ret;
}

static int secp256k1_multischnorr_generate_key_nonces(const secp256k1_context* ctx, secp256k1_scalar* key_mine, secp256k1_scalar* nonce_mine, secp256k1_ge *pubnonce_all, const secp256k1_ge *pubnonce_others, const unsigned char *msg32, const unsigned char *sec32, secp256k1_nonce_function noncefp, const void* ndata) {
    unsigned char sec32t[32];
    int ret;
    int count = 0;

    if (noncefp == NULL) {
        noncefp = secp256k1_nonce_function_default;
    }

    ret = secp256k1_multischnorr_compute_tweaked_privkey(ctx, key_mine, sec32t, sec32);

    while (ret) {
        unsigned char nonce32[32];
        ret = noncefp(nonce32, msg32, sec32t, secp256k1_schnorr_algo16, (void*)ndata, count);
        if (!ret) {
            break;
        }
        ret = secp256k1_schnorr_nonces_set_b32(&ctx->ecmult_gen_ctx, nonce_mine, pubnonce_all, nonce32, pubnonce_others);
        memset(nonce32, 0, 32);
        if (ret) {
            break;
        }
        count++;
    }

    memset(sec32t, 0, 32);

    if (!ret) {
        secp256k1_scalar_clear(key_mine);
        secp256k1_scalar_clear(nonce_mine);
    }
    return ret;
}

int secp256k1_multischnorr_stage1(const secp256k1_context* ctx, unsigned char *stage1, const unsigned char *msg32, const unsigned char *sec32, secp256k1_nonce_function noncefp, const void* noncedata) {
    secp256k1_scalar nonce_mine;
    secp256k1_scalar key_mine;
    secp256k1_ge pubnonce_mine;
    int ret;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(sec32 != NULL);
    ARG_CHECK(stage1 != NULL);

    ret = secp256k1_multischnorr_generate_key_nonces(ctx, &key_mine, &nonce_mine, &pubnonce_mine, NULL, msg32, sec32, noncefp, noncedata);
    secp256k1_scalar_clear(&nonce_mine);
    secp256k1_scalar_clear(&key_mine);
    if (ret) {
        secp256k1_schnorr_ge_get_b32(stage1, &pubnonce_mine);
    } else {
        memset(stage1, 0, 32);
    }
    return ret;
}

int secp256k1_multischnorr_stage2(const secp256k1_context* ctx, unsigned char *stage2, const unsigned char * const *other_stage1s, size_t num_others, const unsigned char *msg32, const unsigned char *sec32, secp256k1_nonce_function noncefp, const void* noncedata) {
    int ret = 1;
    secp256k1_scalar sec, nonce_mine;
    secp256k1_ge pubnonce_others;
    secp256k1_ge pubnonce_all;

    VERIFY_CHECK(ctx != NULL);
    ARG_CHECK(secp256k1_ecmult_gen_context_is_built(&ctx->ecmult_gen_ctx));
    ARG_CHECK(secp256k1_ecmult_context_is_built(&ctx->ecmult_ctx));
    ARG_CHECK(stage2 != NULL);
    if (num_others > 0) {
        ARG_CHECK(other_stage1s != NULL);
        ARG_CHECK(other_stage1s[num_others - 1] != NULL);
    }
    ARG_CHECK(msg32 != NULL);
    ARG_CHECK(sec32 != NULL);

    if (num_others > 0) {
        secp256k1_gej pubnoncej_others;
        size_t n = 0;
        while (n < num_others) {
            secp256k1_ge tmppub;
            ret = ret & secp256k1_schnorr_ge_set_b32(&tmppub, other_stage1s[n]);
            if (!ret) {
                break;
            }
            if (n) {
                secp256k1_gej_add_ge(&pubnoncej_others, &pubnoncej_others, &tmppub);
            } else {
                secp256k1_gej_set_ge(&pubnoncej_others, &tmppub);
            }
            n++;
        }
        if (ret) {
            secp256k1_ge_set_gej(&pubnonce_others, &pubnoncej_others);
        }
    }

    ret = ret && secp256k1_multischnorr_generate_key_nonces(ctx, &sec, &nonce_mine, &pubnonce_all, num_others > 0 ? &pubnonce_others : NULL, msg32, sec32, noncefp, noncedata);
    ret = ret && secp256k1_schnorr_sig_sign(stage2, &sec, &nonce_mine, &pubnonce_all, secp256k1_schnorr_msghash_sha256, msg32);
    secp256k1_scalar_clear(&sec);
    secp256k1_scalar_clear(&nonce_mine);
    if (!ret) {
        memset(stage2, 0, 64);
    }
    return ret;
}

int secp256k1_multischnorr_combine_sigs(const secp256k1_context* ctx, unsigned char *sig64, const unsigned char * const *stage2s, size_t n) {
    ARG_CHECK(sig64 != NULL);
    ARG_CHECK(n >= 1);
    ARG_CHECK(stage2s != NULL);
    ARG_CHECK(stage2s[n - 1] != NULL);
    return secp256k1_schnorr_sig_combine(sig64, n, stage2s);
}

int secp256k1_multischnorr_combine_keys(const secp256k1_context* ctx, secp256k1_pubkey *pubcomb, const secp256k1_pubkey * const *pub, size_t n) {
    size_t i;
    secp256k1_gej Qj, pubcombj;
    secp256k1_ge Q;
    int ret = 1;

    ARG_CHECK(pubcomb != NULL);
    ARG_CHECK(n >= 1);
    ARG_CHECK(pub != NULL);

    secp256k1_gej_set_infinity(&pubcombj);

    for (i = 0; i < n; i++) {
        secp256k1_pubkey_load(ctx, &Q, pub[i]);
        ret = ret && secp256k1_multischnorr_compute_tweaked_pubkey(ctx, &Qj, &Q);
        secp256k1_gej_add_var(&pubcombj, &pubcombj, &Qj, NULL);
        ret = ret && !secp256k1_gej_is_infinity(&pubcombj);
    }
    if (!ret) {
        memset(pubcomb, 0, sizeof(*pubcomb));
    } else {
       secp256k1_ge_set_gej_var(&Q, &pubcombj);
       secp256k1_pubkey_save(pubcomb, &Q);
    }
    return ret;
}


#endif
