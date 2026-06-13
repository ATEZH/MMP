#include <assert.h>
#include <gmp.h>
#include <process.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "../bigint.h"

#ifndef ITER
#define ITER 50000
#endif

#ifndef MAX_BITS
#define MAX_BITS 1024
#endif

static void failf(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    exit(EXIT_FAILURE);
}

static char *mpz_to_str_dec(mpz_t z) { return mpz_get_str(NULL, 10, z); }

static BigInt *bigint_from_mpz(mpz_t z) {
    char *s = mpz_to_str_dec(z);
    BigInt *b = bigint_init_from_str(s);
    free(s);
    return b;
}

static void check_invariants(BigInt *b) {
    if (b == NULL) failf("Invariant failure: BigInt *pointer NULL\n");
    if (b->size < 1) failf("Invariant failure: size < 1 (%d)\n", b->size);
    if (b->capacity < b->size) failf("Invariant failure: capacity < size (%d < %d)\n", b->capacity, b->size);
    if (b->capacity < 16) failf("Invariant failure: capacity < 16 (%d)\n", b->capacity);
    if (b->size > 1 && b->limbs[b->size - 1] == 0) failf("Invariant failure: top limb zero for size > 1\n");
    if (!(b->sign == 1 || b->sign == -1)) failf("Invariant failure: sign not 1 or -1 (%d)\n", b->sign);
}

static int compare_bigint_mpz(BigInt *b, mpz_t z) {
    char *s_gmp = mpz_to_str_dec(z);
    char *s_my = bigint_to_str(b);
    int eq = (strcmp(s_gmp, s_my) == 0);
    if (!eq) {
        fprintf(stderr, "Mismatch:\n  gmp: %s\n  my : %s\n", s_gmp, s_my);
    }
    free(s_gmp);
    free(s_my);
    return eq;
}

static void rand_mpz(mpz_t out, gmp_randstate_t state, unsigned bits) {
    if (bits == 0) {
        mpz_set_ui(out, 0);
        return;
    }
    mpz_urandomb(out, state, bits);

    if (gmp_urandomb_ui(state, 1)) {
        mpz_neg(out, out);
    }
}

static void test_init_and_basic(void) {
    printf("[TEST] init and basic conversions\n");
    BigInt *b = bigint_init();
    assert(b != NULL);
    check_invariants(b);

    assert(bigint_is_zero(b));
    assert(bigint_sign(b) == 1);
    char *s = bigint_to_str(b);
    assert(strcmp(s, "0") == 0);
    free(s);

    BigInt *a = bigint_init_from_uint64(0ULL, 1);
    check_invariants(a);
    assert(bigint_is_zero(a));
    bigint_destroy(a);

    a = bigint_init_from_uint64(1ULL, 1);
    s = bigint_to_str(a);
    assert(strcmp(s, "1") == 0);
    free(s);
    bigint_destroy(a);

    a = bigint_init_from_uint64(UINT64_MAX, 1);
    s = bigint_to_str(a);

    mpz_t tmp;
    mpz_init(tmp);
    mpz_set_ui(tmp, 0);
    mpz_set_str(tmp, "18446744073709551615", 10);
    char *g = mpz_get_str(NULL, 10, tmp);
    assert(strcmp(g, s) == 0);
    free(g);
    mpz_clear(tmp);
    free(s);
    bigint_destroy(b);

    BigInt *p = bigint_init_from_str("0");
    assert(bigint_is_zero(p));
    bigint_destroy(p);

    BigInt *n = bigint_init_from_str("-123456789012345678901234567890");
    char *ns = bigint_to_str(n);
    assert(strcmp(ns, "-123456789012345678901234567890") == 0);
    free(ns);
    check_invariants(n);
    bigint_destroy(n);

    BigInt *one = bigint_init();
    positive_one_bigint(one);
    s = bigint_to_str(one);
    assert(strcmp(s, "1") == 0);
    free(s);
    bigint_destroy(one);

    printf("  OK\n");
}

static void test_comparisons_and_cmp_uint_variants(gmp_randstate_t state) {
    printf("[TEST] comparisons (bigint_cmp, abs, uint64/int64 variants)\n");

    BigInt *z = bigint_init_from_str("0");
    BigInt *p = bigint_init_from_str("12345");
    BigInt *q = bigint_init_from_str("-12345");

    assert(bigint_cmp(p, p) == 0);
    assert(bigint_abs_cmp(p, q) == 0);
    assert(bigint_cmp(q, p) < 0);
    assert(bigint_cmp_uint64(p, 12345ULL) == 0);
    assert(bigint_abs_cmp_uint64(p, 12345ULL) == 0);
    assert(bigint_cmp_int64(q, -12345LL) == 0);
    bigint_destroy(z);
    bigint_destroy(p);
    bigint_destroy(q);

    for (int i = 0; i < ITER; ++i) {
        unsigned bits = (rand() % (MAX_BITS + 1));
        mpz_t A, B;
        mpz_inits(A, B, NULL);
        rand_mpz(A, state, bits);
        rand_mpz(B, state, bits);
        BigInt *a = bigint_from_mpz(A);
        BigInt *b = bigint_from_mpz(B);

        mpz_t cmp;
        mpz_init(cmp);
        int gcmp = mpz_cmp(A, B);
        int mycmp = bigint_cmp(a, b);

        if (gcmp < 0)
            gcmp = -1;
        else if (gcmp > 0)
            gcmp = 1;
        if (mycmp < 0)
            mycmp = -1;
        else if (mycmp > 0)
            mycmp = 1;
        if (mycmp != gcmp) {
            char *sa = bigint_to_str(a), *sb = bigint_to_str(b), *ga = mpz_to_str_dec(A), *gb = mpz_to_str_dec(B);
            failf("cmp mismatch: gmp(%s vs %s)=%d my(%s vs %s)=%d\n", ga, gb, gcmp, sa, sb, mycmp);
            free(sa);
            free(sb);
            free(ga);
            free(gb);
        }

        int gabs = mpz_cmpabs(A, B);
        if (gabs < 0)
            gabs = -1;
        else if (gabs > 0)
            gabs = 1;
        int myabs = bigint_abs_cmp(a, b);
        if (myabs < 0)
            myabs = -1;
        else if (myabs > 0)
            myabs = 1;
        if (gabs != myabs) {
            failf("abs cmp mismatch\n");
        }

        if (mpz_sizeinbase(A, 2) <= 64) {
            uint64_t v = mpz_get_ui(A);
            int r = bigint_cmp_uint64(a, v);
            int rg;

            rg = mpz_cmp_ui(A, v);
            if ((r < 0 ? -1 : (r > 0 ? 1 : 0)) != (rg < 0 ? -1 : (rg > 0 ? 1 : 0))) failf("cmp_uint64 mismatch\n");
        }
        if (mpz_sizeinbase(A, 2) <= 63) {
            long rv = mpz_get_si(A);
            int r = bigint_cmp_int64(a, rv);
            int rg = mpz_cmp_si(A, rv);
            if ((r < 0 ? -1 : (r > 0 ? 1 : 0)) != (rg < 0 ? -1 : (rg > 0 ? 1 : 0))) failf("cmp_int64 mismatch\n");
        }

        check_invariants(a);
        check_invariants(b);

        bigint_destroy(a);
        bigint_destroy(b);
        mpz_clears(A, B, cmp, NULL);
    }
    printf("  OK\n");
}

static void test_add_sub(gmp_randstate_t state) {
    printf("[TEST] add / sub (uint32/uint64 / bigint)\n");

    BigInt *a = bigint_init_from_uint64(0xFFFFFFFFULL, 1);
    BigInt *b = bigint_init_from_uint64(1ULL, 1);
    BigInt *out = bigint_init();
    bigint_add(a, a, b);

    bigint_destroy(a);
    bigint_destroy(b);

    for (int i = 0; i < ITER; ++i) {
        mpz_t A, B, R;
        mpz_inits(A, B, R, NULL);
        unsigned bitsA = 1 + (rand() % MAX_BITS);
        unsigned bitsB = 1 + (rand() % MAX_BITS);
        rand_mpz(A, state, bitsA);
        rand_mpz(B, state, bitsB);

        BigInt *a = bigint_from_mpz(A);
        BigInt *b = bigint_from_mpz(B);
        BigInt *res = bigint_init();

        bigint_add(res, a, b);
        mpz_add(R, A, B);
        if (!compare_bigint_mpz(res, R)) {
            failf("add failed\n");
        }

        bigint_sub(res, a, b);
        mpz_sub(R, A, B);
        if (!compare_bigint_mpz(res, R)) {
            failf("sub failed\n");
        }

        uint32_t u32 = (uint32_t)(rand());
        bigint_add_uint32(res, a, u32);
        mpz_add_ui(R, A, (unsigned long)u32);
        if (!compare_bigint_mpz(res, R)) failf("add_uint32 failed\n");

        uint64_t u64 = ((uint64_t)rand() << 32) ^ (uint64_t)rand();

        bigint_add_uint64(res, a, u64);

        mpz_t tmp64;
        mpz_init(tmp64);
        mpz_set_ui(tmp64, (unsigned long)(u64 >> 32));
        mpz_mul_2exp(tmp64, tmp64, 32);
        mpz_add_ui(tmp64, tmp64, (unsigned long)(u64 & 0xFFFFFFFFUL));
        mpz_add(R, A, tmp64);
        mpz_clear(tmp64);

        if (!compare_bigint_mpz(res, R)) failf("add_uint64 failed\n");

        check_invariants(res);

        bigint_destroy(a);
        bigint_destroy(b);
        bigint_destroy(res);
        mpz_clears(A, B, R, NULL);
    }
    printf("  OK\n");
}

static void test_mul(gmp_randstate_t state) {
    printf("[TEST] multiplication (uint32 / bigint)\n");

    BigInt *z = bigint_init_from_str("0");
    BigInt *one = bigint_init_from_str("1");
    BigInt *minus_one = bigint_init_from_str("-1");
    BigInt *big = bigint_init_from_str("4294967296");
    BigInt *r = bigint_init();

    bigint_mul(r, z, big);
    assert(bigint_is_zero(r));
    check_invariants(r);

    bigint_mul(r, big, one);
    assert(strcmp(bigint_to_str(r), "4294967296") == 0);
    check_invariants(r);

    bigint_mul(r, big, minus_one);
    assert(strcmp(bigint_to_str(r), "-4294967296") == 0);
    check_invariants(r);

    bigint_mul(r, big, big);
    assert(strcmp(bigint_to_str(r), "18446744073709551616") == 0);
    check_invariants(r);

    bigint_destroy(z);
    bigint_destroy(one);
    bigint_destroy(minus_one);
    bigint_destroy(big);
    bigint_destroy(r);

    for (int i = 0; i < ITER; ++i) {
        mpz_t A, B, R;
        mpz_inits(A, B, R, NULL);
        rand_mpz(A, state, 1 + (rand() % MAX_BITS));
        rand_mpz(B, state, 1 + (rand() % MAX_BITS));
        BigInt *a = bigint_from_mpz(A);
        BigInt *b = bigint_from_mpz(B);
        BigInt *out = bigint_init();

        bigint_mul(out, a, b);
        mpz_mul(R, A, B);
        if (!compare_bigint_mpz(out, R)) {
            printf("a: %s\n", bigint_to_str(a));
            printf("b: %s\n", bigint_to_str(b));
            failf("mul (bigint) failed\n");
        }

        uint32_t u = (uint32_t)(rand());
        bigint_mul_uint32(out, a, u);
        mpz_mul_ui(R, A, (unsigned long)u);
        if (!compare_bigint_mpz(out, R)) failf("mul_uint32 failed\n");

        check_invariants(out);

        bigint_destroy(a);
        bigint_destroy(b);
        bigint_destroy(out);
        mpz_clears(A, B, R, NULL);
    }

    printf("  OK\n");
}

static void test_shifts(gmp_randstate_t state) {
    printf("[TEST] shifts (left/right)\n");
    for (int i = 0; i < ITER; ++i) {
        mpz_t A, L, R;
        mpz_inits(A, L, R, NULL);
        unsigned bits = 1 + (rand() % MAX_BITS);
        rand_mpz(A, state, bits);
        unsigned shift = rand() % 2048;
        BigInt *a = bigint_from_mpz(A);
        BigInt *out = bigint_init();

        bigint_shift_left(out, a, shift);
        mpz_mul_2exp(L, A, shift);
        if (!compare_bigint_mpz(out, L)) failf("shift_left failed (shift=%u)\n", shift);

        bigint_shift_right(out, a, shift);
        mpz_tdiv_q_2exp(R, A, shift);
        if (!compare_bigint_mpz(out, R)) failf("shift_right failed (shift=%u)\n", shift);

        check_invariants(out);
        bigint_destroy(a);
        bigint_destroy(out);
        mpz_clears(A, L, R, NULL);
    }
    printf("  OK\n");
}

static void test_division(gmp_randstate_t state) {
    printf("[TEST] division (uint32 / bigint) - quotient and remainder\n");
    for (int i = 0; i < ITER; ++i) {
        mpz_t A, B, Q, R;
        mpz_inits(A, B, Q, R, NULL);
        rand_mpz(A, state, 1 + (rand() % MAX_BITS));

        do {
            rand_mpz(B, state, 1 + (rand() % MAX_BITS));
        } while (mpz_cmp_ui(B, 0) == 0);

        BigInt *a = bigint_from_mpz(A);
        BigInt *b = bigint_from_mpz(B);
        BigInt *q = bigint_init();
        BigInt *r = bigint_init();

        bigint_div(q, r, a, b);

        mpz_tdiv_qr(Q, R, A, B);

        if (!compare_bigint_mpz(q, Q)) failf("div quotient mismatch\n");
        if (!compare_bigint_mpz(r, R)) failf("div remainder mismatch\n");

        uint32_t dv = (uint32_t)(rand() + rand()) % BASE;
        if (dv == 0) {
            dv = 1;
        }

        bigint_div_uint32(q, r, a, dv);

        unsigned long rem = mpz_tdiv_qr_ui(Q, R, A, (unsigned long)dv);

        if (!compare_bigint_mpz(q, Q)) failf("div_uint32 quotient mismatch\n");

        if (!compare_bigint_mpz(r, R)) failf("div_uint32 remainder mismatch\n");

        check_invariants(q);
        check_invariants(r);

        bigint_destroy(a);
        bigint_destroy(b);
        bigint_destroy(q);
        bigint_destroy(r);
        mpz_clears(A, B, Q, R, NULL);
    }
    printf("  OK\n");
}

static void test_misc_and_stress_final(gmp_randstate_t state) {
    printf("[TEST] misc / final stress rounds (combined operations)\n");

    for (int i = 0; i < ITER; ++i) {
        mpz_t accum_gmp;
        mpz_init(accum_gmp);

        mpz_t cur;
        mpz_init(cur);
        rand_mpz(cur, state, 1 + (rand() % MAX_BITS));
        mpz_set(accum_gmp, cur);
        BigInt *accum = bigint_from_mpz(cur);

        int ops = 1 + (rand() % 50);
        for (int o = 0; o < ops; ++o) {
            int op = rand() % 6;
            mpz_t other;
            mpz_init(other);
            rand_mpz(other, state, 1 + (rand() % MAX_BITS));
            BigInt *other_b = bigint_from_mpz(other);
            switch (op) {
                case 0:
                    bigint_add(accum, accum, other_b);
                    mpz_add(accum_gmp, accum_gmp, other);
                    break;
                case 1:
                    bigint_sub(accum, accum, other_b);
                    mpz_sub(accum_gmp, accum_gmp, other);
                    break;
                case 2:
                    if (mpz_sizeinbase(other, 2) < 512) {
                        bigint_mul(accum, accum, other_b);
                        mpz_mul(accum_gmp, accum_gmp, other);
                    }
                    break;
                case 3: {
                    unsigned sh = rand() % 256;
                    bigint_shift_left(accum, accum, sh);
                    mpz_mul_2exp(accum_gmp, accum_gmp, sh);
                } break;
                case 4: {
                    unsigned sh = rand() % 256;
                    bigint_shift_right(accum, accum, sh);
                    mpz_tdiv_q_2exp(accum_gmp, accum_gmp, sh);
                } break;
                case 5: {
                    uint32_t u = (uint32_t)rand();
                    bigint_add_uint32(accum, accum, u);
                    mpz_add_ui(accum_gmp, accum_gmp, (unsigned long)u);
                } break;
            }
            check_invariants(accum);
            if (!compare_bigint_mpz(accum, accum_gmp)) {
                failf("mixed stress mismatch\n");
            }
            bigint_destroy(other_b);
            mpz_clear(other);
        }
        if (!compare_bigint_mpz(accum, accum_gmp)) failf("mixed stress mismatch\n");
        bigint_destroy(accum);
        mpz_clears(accum_gmp, cur, NULL);
    }
    printf("  OK\n");
}

int main(void) {
    srand((unsigned)time(NULL));

    gmp_randstate_t state;
    gmp_randinit_default(state);
    unsigned long seed = (unsigned long)time(NULL) ^ (unsigned long)getpid();
    gmp_randseed_ui(state, seed);

    test_init_and_basic();
    test_comparisons_and_cmp_uint_variants(state);
    test_add_sub(state);
    test_mul(state);
    test_shifts(state);
    test_division(state);
    test_misc_and_stress_final(state);

    gmp_randclear(state);
    printf("\nAll tests passed.\n");
}
