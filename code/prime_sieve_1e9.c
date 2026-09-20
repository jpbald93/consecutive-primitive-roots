/*
 * prime_sieve_1e9.c  —  segmented sieve with Artin-prime census
 * Uses a segmented Eratosthenes to avoid allocating gigabytes of RAM.
 * Segment size: 2^21 ≈ 2M bytes per block.
 *
 * For each prime p >= 7 up to LIMIT (default 10^9, configurable via argv[1]):
 *   emits p, prev_gap, next_gap, min_gap, loneliness, omega(p-1),
 *         is_artin10, pmod4, pmod8, pmod12
 *
 * The last prime in range has next_gap = 0 (unknown); this is recorded
 * explicitly rather than omitted, so the CSV contains every eligible prime.
 *
 * Compile:
 *   gcc -O3 -o prime_sieve_1e9 prime_sieve_1e9.c -lm -lgmp
 *
 * Usage:
 *   ./prime_sieve_1e9 [LIMIT]          # default LIMIT = 1000000000
 *   ./prime_sieve_1e9 1000000 > data_1e6.csv
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <gmp.h>

#define DEFAULT_LIMIT  1000000000L   /* 10^9 */
#define SEG_SIZE       (1 << 21)     /* ~2M per segment */

/* ── tiny sieve for primes up to sqrt(LIMIT) ── */
static char *small_composite = NULL;
static long *small_primes = NULL;
static int   n_small = 0;
static long  small_lim = 0;

void build_small(long limit) {
    small_lim = (long)sqrt((double)limit) + 2;
    small_composite = calloc(small_lim + 1, 1);
    small_primes = malloc((size_t)(small_lim / 2) * sizeof(long));
    for (long i = 2; i <= small_lim; i++) {
        if (!small_composite[i]) {
            small_primes[n_small++] = i;
            for (long j = i*i; j <= small_lim; j += i)
                small_composite[j] = 1;
        }
    }
}

/* ── omega(m): distinct prime factors by trial division ── */
int omega(long m) {
    int c = 0;
    for (long d = 2; d * d <= m; d++) {
        if (m % d == 0) { c++; while (m % d == 0) m /= d; }
    }
    return c + (m > 1);
}

/* ── Artin check: is 10 a primitive root mod p? ── */
int is_artin10(long p) {
    long pm1 = p - 1, tmp = pm1;
    long fac[64]; int nf = 0;
    for (long d = 2; d * d <= tmp; d++) {
        if (tmp % d == 0) { fac[nf++] = d; while (tmp % d == 0) tmp /= d; }
    }
    if (tmp > 1) fac[nf++] = tmp;

    mpz_t base, mod, exp, res;
    mpz_inits(base, mod, exp, res, NULL);
    mpz_set_si(base, 10);
    mpz_set_si(mod, p);

    int ok = 1;
    for (int i = 0; i < nf && ok; i++) {
        mpz_set_si(exp, pm1 / fac[i]);
        mpz_powm(res, base, exp, mod);
        if (mpz_cmp_si(res, 1) == 0) ok = 0;
    }
    mpz_clears(base, mod, exp, res, NULL);
    return ok;
}

int main(int argc, char **argv) {
    long LIMIT = DEFAULT_LIMIT;
    if (argc > 1) {
        LIMIT = atol(argv[1]);
        if (LIMIT < 10) { fprintf(stderr, "LIMIT must be >= 10\n"); return 1; }
    }
    fprintf(stderr, "Sieve limit: %ld\n", LIMIT);

    build_small(LIMIT);
    fprintf(stderr, "Small primes built: %d primes up to %ld\n", n_small, small_lim);

    static char seg[SEG_SIZE];

    /* track previous prime for gap calculation */
    long prev_prime = 5;   /* we start output from p=7 */

    /* Buffer primes from each segment; emit all but the last, carrying the
       last into the next segment so we can compute next_gap. */
    long *buf = malloc(200000 * sizeof(long));
    long buf_n = 0;

    /* pending_prime: the prime waiting for next_gap information.
       -1 means no prime is pending yet. */
    long pending_prime = -1;

    printf("p,prev_gap,next_gap,min_gap,loneliness,omega_pm1,is_artin10,pmod4,pmod8,pmod12\n");
    fflush(stdout);

    /* ── segmented sieve ── */
    for (long low = 2; low <= LIMIT; low += SEG_SIZE) {
        long high = low + SEG_SIZE - 1;
        if (high > LIMIT) high = LIMIT;
        long len = high - low + 1;

        memset(seg, 0, len);

        /* sieve this segment */
        for (int i = 0; i < n_small; i++) {
            long sp = small_primes[i];
            if (sp * sp > high) break;
            long start = ((low + sp - 1) / sp) * sp;
            if (start == sp) start += sp;
            for (long j = start; j <= high; j += sp)
                seg[j - low] = 1;
        }
        if (low == 2) { seg[0] = 1; seg[1] = 0; /* 2 is prime */ }

        /* collect primes >= 7 in this segment */
        buf_n = 0;
        for (long i = (low < 7 ? 7 - low : 0); i < len; i++) {
            long p = low + i;
            if (!seg[i] && p >= 7)
                buf[buf_n++] = p;
        }

        /* process buffered primes */
        for (long k = 0; k < buf_n; k++) {
            long p_cur = buf[k];

            /* If there is a pending prime, we can now emit it with next_gap */
            if (pending_prime > 0) {
                long pg = pending_prime - prev_prime;
                long ng = p_cur - pending_prime;
                long mg = pg < ng ? pg : ng;
                double L = (double)mg / log((double)pending_prime);
                int om    = omega(pending_prime - 1);
                int artin = is_artin10(pending_prime);
                printf("%ld,%ld,%ld,%ld,%.6f,%d,%d,%ld,%ld,%ld\n",
                       pending_prime, pg, ng, mg, L, om, artin,
                       pending_prime%4, pending_prime%8, pending_prime%12);
                prev_prime = pending_prime;
            }
            pending_prime = p_cur;
        }

        if (low % 50000000 == 0 || low == 2)
            fprintf(stderr, "  processed up to %ld ...\n", high);
    }

    /* Emit the final prime with next_gap = 0 (unknown) */
    if (pending_prime > 0) {
        long pg = pending_prime - prev_prime;
        long ng = 0;  /* next gap unknown */
        long mg = pg;  /* min_gap = prev_gap since next is unknown */
        double L = (double)mg / log((double)pending_prime);
        int om    = omega(pending_prime - 1);
        int artin = is_artin10(pending_prime);
        printf("%ld,%ld,%ld,%ld,%.6f,%d,%d,%ld,%ld,%ld\n",
               pending_prime, pg, ng, mg, L, om, artin,
               pending_prime%4, pending_prime%8, pending_prime%12);
    }

    fprintf(stderr, "Done. Last prime emitted: %ld\n", pending_prime);
    free(buf);
    free(small_composite);
    free(small_primes);
    return 0;
}
