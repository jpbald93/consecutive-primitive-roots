/*
 * independent_audit_1e9.c — INDEPENDENT recomputation of Paper 1's census.
 *
 * Purpose: Paper 1's FINAL_STATUS.md carries this caveat —
 *   "This is an endpoint repair and full reaggregation, NOT a fresh independent
 *    factorization/order computation for every one of the 50 million primes."
 * This program removes that caveat by recomputing everything from scratch.
 *
 * Deliberately INDEPENDENT of code/prime_sieve_1e9.c:
 *   - no GMP: modular exponentiation uses __int128 mulmod, written here
 *   - p-1 is factored by a SEGMENTED SIEVE OF FACTORS, not by per-prime trial
 *     division (different algorithm, so a bug in one is unlikely to be
 *     mirrored in the other)
 *   - runs as N independent processes over disjoint ranges, stitched afterwards
 *
 * Emits, for a range [lo, hi]:
 *   n_primes, n_artin (base 10),
 *   the 2x2 table of (Artin(p_n), Artin(p_{n+1})) for pairs wholly inside,
 *   boundary info (first/last prime and their Artin status) for stitching,
 *   and the doubly-Artin count restricted to gaps g = 20 and g = 60.
 *
 * Artin base 10: 10 is a primitive root mod p, i.e. 10^((p-1)/q) != 1 (mod p)
 * for every prime q | p-1. Requires p != 2, 5. We census p >= 7.
 *
 * Compile:  gcc -O3 -march=native -o independent_audit_1e9 independent_audit_1e9.c -lm
 * Usage:    ./independent_audit_1e9 <lo> <hi>        # emits one JSON line
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

#define SEG   (1 << 20)      /* 1M numbers per segment */
#define MAXF  16             /* distinct prime factors of n < 2^31 is <= 9 */

static long  *sp = NULL;     /* base primes up to sqrt(hi) */
static int    n_sp = 0;

static void build_base(long hi) {
    long lim = (long)sqrt((double)hi) + 2;
    char *c = calloc(lim + 1, 1);
    sp = malloc(sizeof(long) * (lim / 2 + 16));
    for (long i = 2; i <= lim; i++) {
        if (c[i]) continue;
        sp[n_sp++] = i;
        for (long j = i * i; j <= lim; j += i) c[j] = 1;
    }
    free(c);
}

/* (a*b) % m without overflow, via 128-bit */
static inline uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m) {
    return (uint64_t)(((unsigned __int128)a * b) % m);
}

static inline uint64_t powmod(uint64_t b, uint64_t e, uint64_t m) {
    uint64_t r = 1; b %= m;
    while (e) {
        if (e & 1) r = mulmod(r, b, m);
        b = mulmod(b, b, m);
        e >>= 1;
    }
    return r;
}

int main(int argc, char **argv) {
    long lo = (argc > 1) ? atol(argv[1]) : 7;
    long hi = (argc > 2) ? atol(argv[2]) : 1000000000L;
    if (lo < 7) lo = 7;

    build_base(hi);

    /* per-segment buffers */
    char     *comp = malloc(SEG);
    uint64_t *resid = malloc(sizeof(uint64_t) * SEG);   /* residual cofactor of n-1 */
    uint32_t *fac  = malloc(sizeof(uint32_t) * SEG * MAXF);
    uint8_t  *nf   = malloc(SEG);
    if (!comp || !resid || !fac || !nf) { fprintf(stderr, "oom\n"); return 2; }

    long long n_primes = 0, n_artin = 0;
    long long t[2][2] = {{0,0},{0,0}};      /* t[art(p_n)][art(p_{n+1})] */
    long long g20_pairs = 0, g20_both = 0;  /* gaps 20 and 60 combined */

    long  prev_p = 0; int prev_a = 0;       /* previous prime in stream */
    long  first_p = 0; int first_a = 0;
    long  last_p  = 0; int last_a  = 0;

    for (long base = lo; base <= hi; base += SEG) {
        long top = base + SEG - 1; if (top > hi) top = hi;
        long len = top - base + 1;

        memset(comp, 0, (size_t)len);
        memset(nf,   0, (size_t)len);
        for (long i = 0; i < len; i++) resid[i] = (uint64_t)(base + i - 1); /* n-1 */

        /* primality sieve on [base, top] */
        for (int k = 0; k < n_sp; k++) {
            long q = sp[k];
            if (q * q > top) break;
            long st = (base + q - 1) / q * q;
            if (st < q * q) st = q * q;
            for (long m = st; m <= top; m += q) comp[m - base] = 1;
        }

        /* SIEVE OF FACTORS on the shifted interval [base-1, top-1]:
           for each base prime q, walk its multiples and divide them out.   */
        for (int k = 0; k < n_sp; k++) {
            long q = sp[k];
            long a = base - 1, b = top - 1;
            long st = (a + q - 1) / q * q;
            for (long m = st; m <= b; m += q) {
                long i = m - a;
                if (resid[i] % (uint64_t)q == 0) {
                    if (nf[i] < MAXF) fac[i * MAXF + nf[i]++] = (uint32_t)q;
                    while (resid[i] % (uint64_t)q == 0) resid[i] /= (uint64_t)q;
                }
            }
        }

        for (long i = 0; i < len; i++) {
            long p = base + i;
            if (comp[i]) continue;
            if (p == 5) continue;                 /* 10 not a unit mod 5 */
            n_primes++;

            /* distinct primes dividing p-1: sieved list, plus a large cofactor */
            int a_ok = 1;
            uint64_t pm1 = (uint64_t)(p - 1);
            for (int j = 0; j < nf[i] && a_ok; j++) {
                uint64_t q = fac[i * MAXF + j];
                if (powmod(10, pm1 / q, (uint64_t)p) == 1) a_ok = 0;
            }
            if (a_ok && resid[i] > 1) {           /* leftover prime factor > sqrt */
                if (powmod(10, pm1 / resid[i], (uint64_t)p) == 1) a_ok = 0;
            }
            if (a_ok) n_artin++;

            if (!first_p) { first_p = p; first_a = a_ok; }
            if (prev_p) {
                t[prev_a][a_ok]++;
                long g = p - prev_p;
                if (g == 20 || g == 60) { g20_pairs++; if (prev_a && a_ok) g20_both++; }
            }
            prev_p = p; prev_a = a_ok;
            last_p = p; last_a = a_ok;
        }
    }

    printf("{\"lo\":%ld,\"hi\":%ld,\"n_primes\":%lld,\"n_artin\":%lld,"
           "\"t00\":%lld,\"t01\":%lld,\"t10\":%lld,\"t11\":%lld,"
           "\"first_p\":%ld,\"first_a\":%d,\"last_p\":%ld,\"last_a\":%d,"
           "\"g2060_pairs\":%lld,\"g2060_both\":%lld}\n",
           lo, hi, n_primes, n_artin,
           t[0][0], t[0][1], t[1][0], t[1][1],
           first_p, first_a, last_p, last_a, g20_pairs, g20_both);
    return 0;
}
