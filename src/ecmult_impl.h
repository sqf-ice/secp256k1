/**********************************************************************
 * Copyright (c) 2013, 2014 Pieter Wuille                             *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef _SECP256K1_ECMULT_IMPL_H_
#define _SECP256K1_ECMULT_IMPL_H_

#include "group.h"
#include "scalar.h"
#include "ecmult.h"

/* optimal for 128-bit and 256-bit exponents. */
#define WINDOW_A 5

/** larger numbers may result in slightly better performance, at the cost of
    exponentially larger precomputed tables. */
#ifdef USE_ENDOMORPHISM
/** Two tables for window size 15: 1.375 MiB. */
#define WINDOW_G 15
#else
/** One table for window size 16: 1.375 MiB. */
#define WINDOW_G 16
#endif

/** The number of entries a table with precomputed multiples needs to have. */
#define ECMULT_TABLE_SIZE(w) (1 << ((w)-2))

static void secp256k1_ecmult_odd_multiples_table(int n, secp256k1_gej_t *prej, secp256k1_fe_t *zr, const secp256k1_gej_t *a) {
#ifdef USE_COZ
    secp256k1_coz_t d;
    int i;

    VERIFY_CHECK(!a->infinity);

    secp256k1_coz_dblu_var(&d, &prej[0], a, &zr[0]);
    for (i = 1; i < n; i++)
        secp256k1_coz_zaddu_var(&prej[i], &d, &zr[i], &prej[i-1]);
#else
    secp256k1_gej_t d;
    int i;

    VERIFY_CHECK(!a->infinity);

    prej[0] = *a;
    secp256k1_gej_double_var(&d, &prej[0], NULL);
    secp256k1_fe_set_int(zr, 1);
    for (i = 1; i < n; i++)
        secp256k1_gej_add_var(&prej[i], &prej[i-1], &d, &zr[i]);
#endif
}

static void secp256k1_ecmult_multi_odd_multiples_table(int k, int n, secp256k1_gej_t *prej, secp256k1_fe_t *zr, const secp256k1_gej_t *a) {
    int j;
    for (j = 0; j < k; j++) {
        secp256k1_gej_t aa;
        secp256k1_fe_t z2, z3;
        if (j != 0) {
            secp256k1_fe_sqr(&z2, &prej[n * j - 1].z);
            secp256k1_fe_mul(&z3, &z2, &prej[n * j - 1].z);
            secp256k1_fe_mul(&aa.x, &a[j].x, &z2);
            secp256k1_fe_mul(&aa.y, &a[j].y, &z3);
            secp256k1_fe_mul(&aa.z, &a[j].z, &prej[n * j - 1].z);
            aa.infinity = 0;
        } else {
            aa = a[0];
        }
        secp256k1_ecmult_odd_multiples_table(n, &prej[n * j], &zr[n * j], &aa);
        if (j != 0) {
            secp256k1_fe_mul(zr + n * j, zr + n * j, &a[j].z);
        }
    }

#ifdef VERIFY
    for (j = 1; j < n * k; j++) {
        secp256k1_fe_t zs;
        secp256k1_fe_mul(&zs, &prej[j - 1].z, &zr[j]);
        VERIFY_CHECK(secp256k1_fe_equal_var(&zs, &prej[j].z));
    }
#endif
}

static void secp256k1_ecmult_odd_multiples_table_var(int n, secp256k1_ge_storage_t *pre, const secp256k1_gej_t *a) {
    secp256k1_gej_t *prej = checked_malloc(sizeof(secp256k1_gej_t) * n);
    secp256k1_ge_t *prea = checked_malloc(sizeof(secp256k1_ge_t) * n);
    secp256k1_fe_t *zr = checked_malloc(sizeof(secp256k1_fe_t) * n);
    int i;

    secp256k1_ecmult_odd_multiples_table(n, prej, zr, a);
    secp256k1_ge_set_table_gej_var(n, prea, prej, zr);
    for (i = 0; i < n; i++) {
        secp256k1_ge_to_storage(&pre[i], &prea[i]);
    }
    free(prea);
    free(prej);
    free(zr);
}

static void secp256k1_ecmult_odd_multiples_table_globalz_windowa(secp256k1_ge_t *pre, secp256k1_fe_t *globalz, const secp256k1_gej_t *a) {
    secp256k1_gej_t prej[ECMULT_TABLE_SIZE(WINDOW_A)];
    secp256k1_fe_t zr[ECMULT_TABLE_SIZE(WINDOW_A)];

    secp256k1_ecmult_odd_multiples_table(ECMULT_TABLE_SIZE(WINDOW_A), prej, zr, a);
    secp256k1_ge_globalz_set_table_gej(ECMULT_TABLE_SIZE(WINDOW_A), pre, globalz, prej, zr);
}

static void secp256k1_ecmult_multi_odd_multiples_table_globalz_windowa(int k, secp256k1_ge_t *pre, secp256k1_fe_t *globalz, const secp256k1_gej_t *a) {
    secp256k1_gej_t prej[MAX_MULTI * ECMULT_TABLE_SIZE(WINDOW_A)];
    secp256k1_fe_t zr[MAX_MULTI * ECMULT_TABLE_SIZE(WINDOW_A)];

    secp256k1_ecmult_multi_odd_multiples_table(k, ECMULT_TABLE_SIZE(WINDOW_A), prej, zr, a);
    secp256k1_ge_globalz_set_table_gej(k * ECMULT_TABLE_SIZE(WINDOW_A), pre, globalz, prej, zr);
}

/** The following two macro retrieves a particular odd multiple from a table
 *  of precomputed multiples. */
#define ECMULT_TABLE_GET_GE(r,pre,n,w) do { \
    VERIFY_CHECK(((n) & 1) == 1); \
    VERIFY_CHECK((n) >= -((1 << ((w)-1)) - 1)); \
    VERIFY_CHECK((n) <=  ((1 << ((w)-1)) - 1)); \
    if ((n) > 0) \
        *(r) = (pre)[((n)-1)/2]; \
    else \
        secp256k1_ge_neg((r), &(pre)[(-(n)-1)/2]); \
} while(0)

#define ECMULT_TABLE_GET_GE_STORAGE(r,pre,n,w) do { \
    VERIFY_CHECK(((n) & 1) == 1); \
    VERIFY_CHECK((n) >= -((1 << ((w)-1)) - 1)); \
    VERIFY_CHECK((n) <=  ((1 << ((w)-1)) - 1)); \
    if ((n) > 0) \
        secp256k1_ge_from_storage((r), &(pre)[((n)-1)/2]); \
    else {\
        secp256k1_ge_from_storage((r), &(pre)[(-(n)-1)/2]); \
        secp256k1_ge_neg((r), (r)); \
    } \
} while(0)

typedef struct {
    /* For accelerating the computation of a*P + b*G: */
    secp256k1_ge_storage_t pre_g[ECMULT_TABLE_SIZE(WINDOW_G)];    /* odd multiples of the generator */
#ifdef USE_ENDOMORPHISM
    secp256k1_ge_storage_t pre_g_128[ECMULT_TABLE_SIZE(WINDOW_G)]; /* odd multiples of 2^128*generator */
#endif
} secp256k1_ecmult_consts_t;

static const secp256k1_ecmult_consts_t *secp256k1_ecmult_consts = NULL;

static void secp256k1_ecmult_start(void) {
    secp256k1_gej_t gj;
    secp256k1_ecmult_consts_t *ret;
    if (secp256k1_ecmult_consts != NULL)
        return;

    /* Allocate the precomputation table. */
    ret = (secp256k1_ecmult_consts_t*)checked_malloc(sizeof(secp256k1_ecmult_consts_t));

    /* get the generator */
    secp256k1_gej_set_ge(&gj, &secp256k1_ge_const_g);

    /* precompute the tables with odd multiples */
    secp256k1_ecmult_odd_multiples_table_var(ECMULT_TABLE_SIZE(WINDOW_G), ret->pre_g, &gj);

#ifdef USE_ENDOMORPHISM
    {
        secp256k1_gej_t g_128j;
        int i;
        /* calculate 2^128*generator */
        g_128j = gj;
        for (i = 0; i < 128; i++)
            secp256k1_gej_double_var(&g_128j, &g_128j, NULL);
        secp256k1_ecmult_odd_multiples_table_var(ECMULT_TABLE_SIZE(WINDOW_G), ret->pre_g_128, &g_128j);
    }
#endif

    /* Set the global pointer to the precomputation table. */
    secp256k1_ecmult_consts = ret;
}

static void secp256k1_ecmult_stop(void) {
    secp256k1_ecmult_consts_t *c;
    if (secp256k1_ecmult_consts == NULL)
        return;

    c = (secp256k1_ecmult_consts_t*)secp256k1_ecmult_consts;
    secp256k1_ecmult_consts = NULL;
    free(c);
}

/** Convert a number to WNAF notation. The number becomes represented by sum(2^i * wnaf[i], i=0..bits),
 *  with the following guarantees:
 *  - each wnaf[i] is either 0, or an odd integer between -(1<<(w-1) - 1) and (1<<(w-1) - 1)
 *  - two non-zero entries in wnaf are separated by at least w-1 zeroes.
 *  - the number of set values in wnaf is returned. This number is at most 256, and at most one more
 *  - than the number of bits in the (absolute value) of the input.
 */
static int secp256k1_ecmult_wnaf(int16_t *wnaf, const secp256k1_scalar_t *a, int w) {
    secp256k1_scalar_t s = *a;
    int set_bits = 0;
    int bit = 0;
    int sign = 1;

    if (secp256k1_scalar_get_bits(&s, 255, 1)) {
        secp256k1_scalar_negate(&s, &s);
        sign = -1;
    }

    while (bit < 256) {
        int now;
        int word;
        if (secp256k1_scalar_get_bits(&s, bit, 1) == 0) {
            bit++;
            continue;
        }
        while (set_bits < bit) {
            wnaf[set_bits++] = 0;
        }
        now = w;
        if (bit + now > 256) {
            now = 256 - bit;
        }
        word = secp256k1_scalar_get_bits_var(&s, bit, now);
        if (word & (1 << (w-1))) {
            secp256k1_scalar_add_bit(&s, bit + w);
            wnaf[set_bits++] = sign * (word - (1 << w));
        } else {
            wnaf[set_bits++] = sign * word;
        }
        bit += now;
    }
    return set_bits;
}

static void secp256k1_ecmult(secp256k1_gej_t *r, const secp256k1_gej_t *a, const secp256k1_scalar_t *na, const secp256k1_scalar_t *ng) {
    secp256k1_ge_t pre_a[ECMULT_TABLE_SIZE(WINDOW_A)];
    secp256k1_ge_t tmpa;
    secp256k1_fe_t Z;
    const secp256k1_ecmult_consts_t *c = secp256k1_ecmult_consts;
#ifdef USE_ENDOMORPHISM
    secp256k1_ge_t pre_a_lam[ECMULT_TABLE_SIZE(WINDOW_A)];
    secp256k1_scalar_t na_1, na_lam;
    /* Splitted G factors. */
    secp256k1_scalar_t ng_1, ng_128;
    int16_t wnaf_na_1[130];
    int16_t wnaf_na_lam[130];
    int bits_na_1;
    int bits_na_lam;
    int16_t wnaf_ng_1[129];
    int bits_ng_1;
    int16_t wnaf_ng_128[129];
    int bits_ng_128;
#else
    int16_t wnaf_na[256];
    int bits_na;
    int16_t wnaf_ng[257];
    int bits_ng;
#endif
    int i;
    int bits;

#ifdef USE_ENDOMORPHISM
    /* split na into na_1 and na_lam (where na = na_1 + na_lam*lambda, and na_1 and na_lam are ~128 bit) */
    secp256k1_scalar_split_lambda_var(&na_1, &na_lam, na);

    /* build wnaf representation for na_1 and na_lam. */
    bits_na_1   = secp256k1_ecmult_wnaf(wnaf_na_1,   &na_1,   WINDOW_A);
    bits_na_lam = secp256k1_ecmult_wnaf(wnaf_na_lam, &na_lam, WINDOW_A);
    VERIFY_CHECK(bits_na_1 <= 130);
    VERIFY_CHECK(bits_na_lam <= 130);
    bits = bits_na_1;
    if (bits_na_lam > bits) bits = bits_na_lam;
#else
    /* build wnaf representation for na. */
    bits_na     = secp256k1_ecmult_wnaf(wnaf_na,     na,      WINDOW_A);
    bits = bits_na;
#endif

    /* Calculate odd multiples of a.
     * All multiples are brought to the same Z 'denominator', which is stored
     * in Z. Due to secp256k1' isomorphism we can do all operations pretending
     * that the Z coordinate was 1, use affine addition formulae, and correct
     * the Z coordinate of the result once at the end.
     * The exception is the precomputed G table points, which are actually
     * affine. Compared to the base used for other points, they have a Z ratio
     * of 1/Z, so we can use secp256k1_gej_add_zinv_var, which uses the same
     * isomorphism to efficiently add with a known Z inverse.
     */
    secp256k1_ecmult_odd_multiples_table_globalz_windowa(pre_a, &Z, a);

#ifdef USE_ENDOMORPHISM
    for (i = 0; i < ECMULT_TABLE_SIZE(WINDOW_A); i++)
        secp256k1_ge_mul_lambda(&pre_a_lam[i], &pre_a[i]);

    /* split ng into ng_1 and ng_128 (where gn = gn_1 + gn_128*2^128, and gn_1 and gn_128 are ~128 bit) */
    secp256k1_scalar_split_128(&ng_1, &ng_128, ng);

    /* Build wnaf representation for ng_1 and ng_128 */
    bits_ng_1   = secp256k1_ecmult_wnaf(wnaf_ng_1,   &ng_1,   WINDOW_G);
    bits_ng_128 = secp256k1_ecmult_wnaf(wnaf_ng_128, &ng_128, WINDOW_G);
    if (bits_ng_1 > bits) bits = bits_ng_1;
    if (bits_ng_128 > bits) bits = bits_ng_128;
#else
    bits_ng     = secp256k1_ecmult_wnaf(wnaf_ng,     ng,      WINDOW_G);
    if (bits_ng > bits) bits = bits_ng;
#endif

    secp256k1_gej_set_infinity(r);

    for (i = bits - 1; i >= 0; i--) {
        int n;
        secp256k1_gej_double_var(r, r, NULL);
#ifdef USE_ENDOMORPHISM
        if (i < bits_na_1 && (n = wnaf_na_1[i])) {
            ECMULT_TABLE_GET_GE(&tmpa, pre_a, n, WINDOW_A);
            secp256k1_gej_add_ge_var(r, r, &tmpa);
        }
        if (i < bits_na_lam && (n = wnaf_na_lam[i])) {
            ECMULT_TABLE_GET_GE(&tmpa, pre_a_lam, n, WINDOW_A);
            secp256k1_gej_add_ge_var(r, r, &tmpa);
        }
        if (i < bits_ng_1 && (n = wnaf_ng_1[i])) {
            ECMULT_TABLE_GET_GE_STORAGE(&tmpa, c->pre_g, n, WINDOW_G);
            secp256k1_gej_add_zinv_var(r, r, &tmpa, &Z);
        }
        if (i < bits_ng_128 && (n = wnaf_ng_128[i])) {
            ECMULT_TABLE_GET_GE_STORAGE(&tmpa, c->pre_g_128, n, WINDOW_G);
            secp256k1_gej_add_zinv_var(r, r, &tmpa, &Z);
        }
#else
        if (i < bits_na && (n = wnaf_na[i])) {
            ECMULT_TABLE_GET_GE(&tmpa, pre_a, n, WINDOW_A);
            secp256k1_gej_add_ge_var(r, r, &tmpa);
        }
        if (i < bits_ng && (n = wnaf_ng[i])) {
            ECMULT_TABLE_GET_GE_STORAGE(&tmpa, c->pre_g, n, WINDOW_G);
            secp256k1_gej_add_zinv_var(r, r, &tmpa, &Z);
        }
#endif
    }

    if (!r->infinity) {
        secp256k1_fe_mul(&r->z, &r->z, &Z);
    }
}

static void secp256k1_ecmult_mult(int points, secp256k1_gej_t *r, const secp256k1_gej_t *a, const secp256k1_scalar_t *na, const secp256k1_scalar_t *ng) {
    secp256k1_ge_t pre_a[MAX_MULTI][ECMULT_TABLE_SIZE(WINDOW_A)];
    secp256k1_ge_t tmpa;
    secp256k1_fe_t Z;
    const secp256k1_ecmult_consts_t *c = secp256k1_ecmult_consts;
#ifdef USE_ENDOMORPHISM
    secp256k1_ge_t pre_a_lam[MAX_MULTI][ECMULT_TABLE_SIZE(WINDOW_A)];
    secp256k1_scalar_t na_1[MAX_MULTI], na_lam[MAX_MULTI];
    /* Splitted G factors. */
    secp256k1_scalar_t ng_1, ng_128;
    int16_t wnaf_na_1[MAX_MULTI][130];
    int16_t wnaf_na_lam[MAX_MULTI][130];
    int bits_na_1[MAX_MULTI];
    int bits_na_lam[MAX_MULTI];
    int16_t wnaf_ng_1[129];
    int bits_ng_1;
    int16_t wnaf_ng_128[129];
    int bits_ng_128;
#else
    int16_t wnaf_na[MAX_MULTI][256];
    int bits_na[MAX_MULTI];
    int16_t wnaf_ng[257];
    int bits_ng;
#endif
    int i;
    int bits = 0;
    int k;

    VERIFY_CHECK(points >= 1);
    VERIFY_CHECK(points <= MAX_MULTI);

    for (k = 0; k < points; k++) {
#ifdef USE_ENDOMORPHISM
    /* split na into na_1 and na_lam (where na = na_1 + na_lam*lambda, and na_1 and na_lam are ~128 bit) */
    secp256k1_scalar_split_lambda_var(&na_1[k], &na_lam[k], &na[k]);

    /* build wnaf representation for na_1 and na_lam. */
    bits_na_1[k]   = secp256k1_ecmult_wnaf(wnaf_na_1[k],   &na_1[k],   WINDOW_A);
    bits_na_lam[k] = secp256k1_ecmult_wnaf(wnaf_na_lam[k], &na_lam[k], WINDOW_A);
    VERIFY_CHECK(bits_na_1[k] <= 130);
    VERIFY_CHECK(bits_na_lam[k] <= 130);
    if (bits_na_1[k] > bits) bits = bits_na_1[k];
    if (bits_na_lam[k] > bits) bits = bits_na_lam[k];
#else
    /* build wnaf representation for na. */
    bits_na[k]     = secp256k1_ecmult_wnaf(wnaf_na[k],     &na[k],      WINDOW_A);
    if (bits_na[k] > bits) bits = bits_na[k];
#endif
    }

    /* calculate odd multiples of all a's */
    secp256k1_ecmult_multi_odd_multiples_table_globalz_windowa(points, &pre_a[0][0], &Z, a);

#ifdef USE_ENDOMORPHISM
    for (k = 0; k < points; k++) {
        for (i = 0; i < ECMULT_TABLE_SIZE(WINDOW_A); i++) {
            secp256k1_ge_mul_lambda(&pre_a_lam[k][i], &pre_a[k][i]);
        }
    }
#endif

#ifdef USE_ENDOMORPHISM
    /* split ng into ng_1 and ng_128 (where gn = gn_1 + gn_128*2^128, and gn_1 and gn_128 are ~128 bit) */
    secp256k1_scalar_split_128(&ng_1, &ng_128, ng);

    /* Build wnaf representation for ng_1 and ng_128 */
    bits_ng_1   = secp256k1_ecmult_wnaf(wnaf_ng_1,   &ng_1,   WINDOW_G);
    bits_ng_128 = secp256k1_ecmult_wnaf(wnaf_ng_128, &ng_128, WINDOW_G);
    if (bits_ng_1 > bits) bits = bits_ng_1;
    if (bits_ng_128 > bits) bits = bits_ng_128;
#else
    bits_ng     = secp256k1_ecmult_wnaf(wnaf_ng,     ng,      WINDOW_G);
    if (bits_ng > bits) bits = bits_ng;
#endif

    secp256k1_gej_set_infinity(r);

    for (i = bits-1; i >= 0; i--) {
        int n;
        secp256k1_gej_double_var(r, r, NULL);
#ifdef USE_ENDOMORPHISM
        for (k = 0; k < points; k++) {
        if (i < bits_na_1[k] && (n = wnaf_na_1[k][i])) {
            ECMULT_TABLE_GET_GE(&tmpa, pre_a[k], n, WINDOW_A);
            secp256k1_gej_add_ge_var(r, r, &tmpa);
        }
        if (i < bits_na_lam[k] && (n = wnaf_na_lam[k][i])) {
            ECMULT_TABLE_GET_GE(&tmpa, pre_a_lam[k], n, WINDOW_A);
            secp256k1_gej_add_ge_var(r, r, &tmpa);
        }
        }
        if (i < bits_ng_1 && (n = wnaf_ng_1[i])) {
            ECMULT_TABLE_GET_GE_STORAGE(&tmpa, c->pre_g, n, WINDOW_G);
            secp256k1_gej_add_zinv_var(r, r, &tmpa, &Z);
        }
        if (i < bits_ng_128 && (n = wnaf_ng_128[i])) {
            ECMULT_TABLE_GET_GE_STORAGE(&tmpa, c->pre_g_128, n, WINDOW_G);
            secp256k1_gej_add_zinv_var(r, r, &tmpa, &Z);
        }
#else
        for (k = 0; k < points; k++) {
        if (i < bits_na[k] && (n = wnaf_na[k][i])) {
            ECMULT_TABLE_GET_GE(&tmpa, pre_a[k], n, WINDOW_A);
            secp256k1_gej_add_ge_var(r, r, &tmpa);
        }
        }
        if (i < bits_ng && (n = wnaf_ng[i])) {
            ECMULT_TABLE_GET_GE_STORAGE(&tmpa, c->pre_g, n, WINDOW_G);
            secp256k1_gej_add_zinv_var(r, r, &tmpa, &Z);
        }
#endif
    }

    if (!r->infinity) {
        secp256k1_fe_mul(&r->z, &r->z, &Z);
    }
}

#endif
