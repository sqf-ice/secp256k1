/**********************************************************************
 * Copyright (c) 2015 Pieter Wuille                                   *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

#include "include/secp256k1.h"
#include "bench.h"

static void bench_start(void* arg) {
    int i;
    (void)arg;
    for (i = 0; i < 5; i++) {
        secp256k1_start(SECP256K1_START_SIGN | SECP256K1_START_VERIFY);
        secp256k1_stop();
    }
}

int main(void) {
    run_benchmark("start", bench_start, NULL, NULL, NULL, 10, 5);
    return 0;
}
