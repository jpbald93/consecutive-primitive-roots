# Independent recomputation of the Paper 1 census — 2026-09-11

## What this removes

`FINAL_STATUS.md` carried this standing caveat:

> This is an endpoint repair and full reaggregation, **not** a fresh independent
> factorization/order computation for every one of the 50 million primes.
> The earlier independent audit checked all prime statuses through 10^6;
> this final pass independently reran the smaller 10^5 detailed check.

That caveat no longer applies. Every one of the 50,847,531 primes has now had
its Artin status recomputed from scratch, on different hardware, by a program
that shares no code with the original sieve.

**Result: the published census is reproduced exactly, in every quantity.**

## What was run

`code/independent_audit_1e9.c`, written specifically as a *disjoint*
implementation of the same census. Deliberate differences from
`code/prime_sieve_1e9.c`:

| | original (`prime_sieve_1e9.c`) | independent (`independent_audit_1e9.c`) |
|---|---|---|
| modular exponentiation | GMP (`mpz_powm`) | hand-written `__int128` `mulmod`/`powmod`, no GMP |
| factorization of `p-1` | per-prime trial division | **segmented sieve of factors** over the shifted interval |
| execution | single stream | 32 independent processes over disjoint ranges, stitched |
| machine | this VM (2-core Xeon E5-2673 v4) | jack — AMD Ryzen AI MAX+ 395, 32 cores, gcc 15.2.0 |

The point of using a different factorization *algorithm* is that a bug in one
is unlikely to be mirrored in the other. Re-running the same program on the
same data would only have tested the hardware.

## Validation before the full run

Both implementations were checked against SymPy at 10^6 — an authority
independent of both:

```
independent_audit_1e9.c : n_primes=78495 n_artin=29500 t=[[30204,18791],[18791,10708]] g2060=2497 both=0
SymPy (n_order)         : n_primes=78495 n_artin=29500 t=[[30204,18791],[18791,10708]] g2060=2497 both=0
```

Exact agreement across all three routes (VM binary, jack binary, SymPy).

## Result at 10^9

32 shards tiling `[7, 10^9]`, contiguity asserted (no gap, no overlap), plus the
31 consecutive-prime pairs straddling shard boundaries added back by
`code/stitch_audit.py` — the only non-additive step in the stitch.

```
quantity                    independent              published  match
n_primes                     50,847,531             50,847,531  OK
n_artin                      19,016,617             19,016,617  OK
n_pairs                      50,847,530             50,847,530  OK
g2060_pairs                   2,195,882              2,195,882  OK
g2060_both                            0                      0  OK
table            [[19758045, 12072868], [12072869, 6943748]]  (identical)  OK
delta                   -0.014140158840        -0.014140158840  OK
chi2                 10166.663432261086     10166.663432261103  OK

INDEPENDENT AUDIT: PASS — published census reproduced exactly
```

`chi2` differs in the 12th significant figure (…086 vs …103). This is
floating-point summation order, not a discrepancy: the 2x2 integer table from
which it is computed is identical, so the two chi-square values are the same
real number evaluated by different orderings. Every integer quantity matches
exactly.

Note in particular **`g2060_both = 0`**: the theorem of Paper 1 — that primes
with gap `g ≡ 20 (mod 40)` can never both be Artin base 10 — is confirmed
independently over all 2,195,882 such pairs below 10^9.

## Runtime

Under 60 seconds wall-clock for the full 10^9 census, on 32 cores. (The
original single-stream run took substantially longer; this is parallelism, not
a better algorithm.)

## Artifacts

On jack, `/tmp/p1_audit/`:

```
0f671045c1bd48507db62ecf0523f95c28495220953e0267666eefbcdc375f03  independent_audit_1e9.c
fc1e0d2401efedb067d62c7b3056057ba757ca51a60da0049bf87d4c90b08c3e  stitch_audit.py
a12212c25e8f291c2ff0d623961fbedfea86a2ea6c604559e456c430a584da45  independent_audit_result.json
5e520824ab599d8dbf93393e75875a7c52b48035d7902fa7889d324821bfdb99  (cat shard_*.json)
```

The two source files are byte-identical to the copies in `code/` (SHA-256
verified on both machines after base64 transfer). Reproduce with:

```
gcc -O3 -march=native -o ia code/independent_audit_1e9.c -lm
# 32 shards over [7,1e9], or any partition; then:
python3 code/stitch_audit.py shard_*.json     # exits non-zero on any mismatch
```

## What this does and does not establish

**Does:** the Artin-status census, the 2x2 contingency table, δ, the Pearson
statistic, and the gap-20/60 exclusion count are all correct, computed twice by
independent means.

**Does not:** this is a recomputation, not a proof of the asymptotic claims. The
conditioning statistics remain descriptive selected-cell quantities; no
limiting correlation is established. The other caveats in `FINAL_STATUS.md`
(typesetting, bibliography, journal policy, author approval) are untouched.
