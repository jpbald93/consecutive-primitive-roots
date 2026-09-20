# Correlations between primitive root statuses of consecutive primes

Reproduction package for the paper of the same name.

Call a prime $p$ an **Artin prime for base 10** if 10 is a primitive root
modulo $p$ — equivalently, if the decimal expansion of $1/p$ has maximal
period $p-1$. This paper asks whether the Artin statuses of *consecutive*
primes are independent. They are not.

Two results:

- **An exact exclusion law (proved, and machine-checked in Lean 4).** If
  $p$ and $p+g$ are both primes exceeding 5 and $g \equiv 20 \pmod{40}$, then
  10 is a quadratic residue modulo exactly one of them, so they can never
  *both* be Artin primes base 10. Verified computationally with no exceptions
  among 194,296,748 such pairs below $10^{11}$.

- **A measured anticorrelation.** Over all 50,847,530 consecutive prime pairs
  below $10^9$,
  $\delta = P(\text{Artin}_{n+1} \mid \text{Artin}_n) - P(\text{Artin}_{n+1} \mid \neg\text{Artin}_n) = -0.014140$.

## Layout

```
paper/     manuscript (LaTeX source + PDF) and the figure script
code/      the census programs and the analysis scripts
results/   summary outputs, logs, and the audit records
lean/      Lean 4 formalisation of the exclusion law
```

## Reproducing the census

Two independent implementations are included. This is deliberate: an audit
that re-runs the same program only tests the hardware.

| | `prime_sieve_1e9.c` | `independent_audit_1e9.c` |
|---|---|---|
| modular exponentiation | GMP `mpz_powm` | hand-written `__int128` |
| factorisation of $p-1$ | per-prime trial division | segmented sieve of factors |

They share no code. Both were checked against SymPy at $10^6$ before use, and
they agree exactly at $10^9$ on every reported quantity.

```bash
# original implementation (requires libgmp)
gcc -O3 -o prime_sieve_1e9 code/prime_sieve_1e9.c -lm -lgmp
./prime_sieve_1e9 1000000000 > data_1e9.csv
python3 code/recompute_corrected.py           # contingency tables, delta, chi^2

# independent implementation (no GMP; shardable, emits one JSON line per range)
gcc -O3 -march=native -o ia code/independent_audit_1e9.c -lm
./ia 7 1000000000 > shard_00.json
python3 code/stitch_audit.py shard_*.json     # exits non-zero on any mismatch
```

`stitch_audit.py` compares against the published census and fails loudly if
anything differs. Sharding is safe: the pairs straddling shard boundaries are
added back, and re-sharding $10^{10}$ under a different partition reproduces
every quantity identically, including $\delta$ to fifteen decimal places.

The full per-prime CSV (several GB) is not distributed; regenerate it with the
sieve above. `results/dataset_sha256.txt` records its hash.

## Reproducing the theorem check

```bash
python3 code/verify_theorem.py               # exclusion law, direct check
python3 code/verify_sieve_small_bound.py     # sieve output vs SymPy at small bound
```

## Lean 4 formalisation

```bash
cd lean
lake exe cache get    # mathlib binary cache — do this first
./gate.sh             # => PASS (11 theorems, standard axioms only)
```

Fetch the cache before building. Without it, `lake` compiles Mathlib from
source, which takes hours and tens of gigabytes.

`Artin/Exclusion.lean` proves the character statement on `ZMod 40`;
`Artin/Bridge.lean` connects it to Mathlib's genuine `legendreSym` via the
second supplementary law and quadratic reciprocity.

The two proof files here are byte-identical to those in the author's full
development, where the equivalent gate passes over a larger set of theorems.
The `EXPECTED_MIN` in this repository's `gate.sh` is set to 11, the number of
non-private declarations in these two files.

`gate.sh` checks three things: the sources contain no `sorry`, `axiom` or
`native_decide`; the build succeeds (by exit status, not by matching a success
string); and every audited declaration depends only on Lean's three standard
axioms — `propext`, `Classical.choice`, `Quot.sound`. The expected number of
audit lines is pinned, so silently deleting a `#print axioms` line fails the
gate rather than passing vacuously.

## Independent verification

The census has been recomputed from scratch by the disjoint implementation
above, on different hardware with a different compiler, reproducing every
published quantity exactly. It was then extended:

| $x$ | primes | $\delta(x)$ | gap-20/60 pairs | doubly Artin |
|---|---|---|---|---|
| $10^9$ | 50,847,531 | $-0.014140$ | 2,195,882 | 0 |
| $10^{10}$ | 455,052,508 | $-0.014723$ | 20,700,958 | 0 |
| $10^{11}$ | 4,118,054,810 | $-0.014998$ | 194,296,748 | 0 |

At each cutoff the prime count equals $\pi(x)$ less the three excluded primes
2, 3, 5, and the Artin density matches Artin's constant to six decimal places
at $10^{10}$ and $10^{11}$.

A note on what the $\delta$ column does **not** show: the magnitude grows with
decreasing increments, but four cutoffs do not determine an eventual limit or
rate. `results/PREREGISTERED_1e11.md` records a prediction made before the
$10^{11}$ run; it was wrong by about ten standard errors. See the discussion
in the paper, which gives an explicit function fitting all four values exactly
while still tending to zero.

## Audit records

`results/` contains the independent-recomputation record, the $10^{10}$ and
$10^{11}$ results, the pre-registered prediction, and an adversarial referee
audit of the non-computational content. They are included because the
corrections they prompted are part of the paper's history.

## Licence

The manuscript, figures and prose are under **CC BY 4.0**
(`LICENSE-CC-BY-4.0.txt`). The code and Lean development are under the **MIT
Licence** (`LICENSE`).

## Status

Preprint; not peer reviewed, not yet submitted to a journal.
