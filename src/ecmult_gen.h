/**********************************************************************
 * Copyright (c) 2013, 2014 Pieter Wuille                             *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#ifndef SECP256K1_ECMULT_GEN_H
#define SECP256K1_ECMULT_GEN_H

#include "scalar.h"
#include "group.h"

#define USE_COMB 1

#if USE_COMB

#if defined(EXHAUSTIVE_TEST_ORDER)

  /* We need to control these values for exhaustive tests because
   * the tables cannot have infinities in them (secp256k1_ge_storage
   * doesn't support infinities) */
#  if EXHAUSTIVE_TEST_ORDER > 32
#    define COMB_BLOCKS 52
#    define COMB_TEETH 5
#  elif EXHAUSTIVE_TEST_ORDER > 16
#    define COMB_BLOCKS 64
#    define COMB_TEETH 4
#  elif EXHAUSTIVE_TEST_ORDER > 8
#    define COMB_BLOCKS 86
#    define COMB_TEETH 3
#  elif EXHAUSTIVE_TEST_ORDER > 4
#    define COMB_BLOCKS 128
#    define COMB_TEETH 2
#  else
#    define COMB_BLOCKS 256
#    define COMB_TEETH 1
#  endif

#  define COMB_SPACING 1

#else

  /* COMB_BLOCKS, COMB_TEETH, COMB_SPACING must all be positive and the product of the three (COMB_BITS)
   * must evaluate to a value in the range [256, 288]. The resulting memory usage for precomputation
   * will be COMB_POINTS_TOTAL * sizeof(secp256k1_ge_storage). */
  #define COMB_BLOCKS 4
  #define COMB_TEETH 5
  #define COMB_SPACING 13

#endif

#if !(1 <= COMB_BLOCKS && COMB_BLOCKS <= 256)
#  error "COMB_BLOCKS must be in the range [1, 256]"
#endif
#if !(1 <= COMB_TEETH && COMB_TEETH <= 8)
#  error "COMB_TEETH must be in the range [1, 8]"
#endif
#if !(1 <= COMB_SPACING && COMB_SPACING <= 256)
#  error "COMB_SPACING must be in the range [1, 256]"
#endif

/* The remaining COMB_* parameters are derived values, don't modify these. */
#define COMB_BITS (COMB_BLOCKS * COMB_TEETH * COMB_SPACING)
#define COMB_GROUPED ((COMB_SPACING == 1) && ((32 % COMB_TEETH) == 0))
#define COMB_OFFSET (COMB_BITS == 256)
#define COMB_POINTS (1 << (COMB_TEETH - 1))
#define COMB_POINTS_TOTAL (COMB_BLOCKS * COMB_POINTS)
#define COMB_MASK (COMB_POINTS - 1)

#if !(256 <= COMB_BITS && COMB_BITS <= 288)
#  error "COMB_BITS must be in the range [256, 288]"
#endif

#else

#if ECMULT_GEN_PREC_BITS != 2 && ECMULT_GEN_PREC_BITS != 4 && ECMULT_GEN_PREC_BITS != 8
#  error "Set ECMULT_GEN_PREC_BITS to 2, 4 or 8."
#endif
#define ECMULT_GEN_PREC_B ECMULT_GEN_PREC_BITS
#define ECMULT_GEN_PREC_G (1 << ECMULT_GEN_PREC_B)
#define ECMULT_GEN_PREC_N (256 / ECMULT_GEN_PREC_B)

#endif

typedef struct {
#if USE_COMB
    /* Precomputation data for the signed-digit multi-comb algorithm as described in section 3.3 of:
     *     "Fast and compact elliptic-curve cryptography", Mike Hamburg
     *         (https://eprint.iacr.org/2012/309)
     */
    secp256k1_ge_storage (*prec)[COMB_BLOCKS][COMB_POINTS];
#if COMB_OFFSET
    /* Signed recoding of a 256-bit scalar must be at least 257 bits, with the top bit always 1. We
     * support a 256-bit comb over a 257-bit recoding by pre-adding an 'offset' value to the context's
     * 'initial' value, to account for the high 1 bit. Note that the 'offset' is calculated to allow
     * for the (COMB_SPACING - 1) doublings in the _ecmult_gen ladder.
     */
    secp256k1_ge offset;
#endif
#else
    /* For accelerating the computation of a*G:
     * To harden against timing attacks, use the following mechanism:
     * * Break up the multiplicand into groups of PREC_B bits, called n_0, n_1, n_2, ..., n_(PREC_N-1).
     * * Compute sum(n_i * (PREC_G)^i * G + U_i, i=0 ... PREC_N-1), where:
     *   * U_i = U * 2^i, for i=0 ... PREC_N-2
     *   * U_i = U * (1-2^(PREC_N-1)), for i=PREC_N-1
     *   where U is a point with no known corresponding scalar. Note that sum(U_i, i=0 ... PREC_N-1) = 0.
     * For each i, and each of the PREC_G possible values of n_i, (n_i * (PREC_G)^i * G + U_i) is
     * precomputed (call it prec(i, n_i)). The formula now becomes sum(prec(i, n_i), i=0 ... PREC_N-1).
     * None of the resulting prec group elements have a known scalar, and neither do any of
     * the intermediate sums while computing a*G.
     */
    secp256k1_ge_storage (*prec)[ECMULT_GEN_PREC_N][ECMULT_GEN_PREC_G]; /* prec[j][i] = (PREC_G)^j * i * G + U_i */
#endif
    secp256k1_scalar blind;
    secp256k1_gej initial;
} secp256k1_ecmult_gen_context;

static const size_t SECP256K1_ECMULT_GEN_CONTEXT_PREALLOCATED_SIZE;
static void secp256k1_ecmult_gen_context_init(secp256k1_ecmult_gen_context* ctx);
static void secp256k1_ecmult_gen_context_build(secp256k1_ecmult_gen_context* ctx, void **prealloc);
static void secp256k1_ecmult_gen_context_finalize_memcpy(secp256k1_ecmult_gen_context *dst, const secp256k1_ecmult_gen_context* src);
static void secp256k1_ecmult_gen_context_clear(secp256k1_ecmult_gen_context* ctx);
static int secp256k1_ecmult_gen_context_is_built(const secp256k1_ecmult_gen_context* ctx);

/** Multiply with the generator: R = a*G */
static void secp256k1_ecmult_gen(const secp256k1_ecmult_gen_context* ctx, secp256k1_gej *r, const secp256k1_scalar *a);

static void secp256k1_ecmult_gen_blind(secp256k1_ecmult_gen_context *ctx, const unsigned char *seed32);

#endif /* SECP256K1_ECMULT_GEN_H */
