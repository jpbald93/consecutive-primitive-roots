# Correlations between primitive root statuses of consecutive primes

Start with `START_HERE.md`. The manuscript in `paper/` is definitive.

Reproduction code and data-generation pipeline for the paper:

> **Correlations between primitive root statuses of consecutive primes**
> Josh Bald (Independent Researcher)
> ORCID: [0009-0002-1317-6489](https://orcid.org/0009-0002-1317-6489)

The paper (`paper/consecutive_artin.pdf`) studies whether the Artin statuses of
*consecutive* primes are correlated. Call a prime `p` an **Artin prime for base 10**
if 10 is a primitive root mod `p` (equivalently, `1/p` has maximal decimal period
`p-1` — a "full reptend" prime).

## Main results

Computing Artin status for all **50,847,531 primes** from 7 to 999,999,937
(the largest prime ≤ 10⁹):

1. **Exclusion law (Theorem 1, proved).** If `p` and `p+g` are primes with `p, p+g > 5`
   and `g ≡ 20 (mod 40)`, then the Legendre symbols `(10|p)` and `(10|p+g)` have
   opposite sign — so **at most one of them can be an Artin prime for base 10**.
   Empirically: among **2,195,882** consecutive pairs with gap 20 or 60 there is
   **not a single** doubly-Artin pair, exactly as the theorem requires.
   Conversely `g ≡ 0 (mod 40)` preserves quadratic-residue status.

2. **Global anticorrelation.** Over all 50,847,530 consecutive pairs,
   `δ = P(Art_{n+1} | Art_n) − P(Art_{n+1} | ¬Art_n) = −0.01414`
   (Pearson χ² = 10,167 on 1 df; nominal signed √ = −100.8).

3. **Gap structure.** `δ(g)` ranges from **−0.592** at `g = 60` (theorem-forced)
   to **+0.643** at `g = 40`, with sign predicted by `g mod 40` and `g mod 3`.

4. **Residue conditioning.** Conditioning on joint residues of `(p_n, p_{n+1})`
   mod 120 or mod 840 substantially reduces a selected-cell signed residual
   metric; the remaining association is small but not established to vanish.
   These are descriptive statistics, not a formal decomposition.

5. **ω repulsion.** `r(ω(p_n − 1), ω(p_{n+1} − 1)) = −0.0410` — the
   factorisations of `p − 1` for consecutive primes repel.

## Endpoint correction (September 2026)

An earlier version of the sieve contained two endpoint bugs: a duplicate row
for `p = 7` and an omitted final prime `p = 999,999,937`. These have been
corrected. The duplicate was already skipped by the analysis scripts; the
missing endpoint adds one non-Artin/non-Artin pair at gap 8. The corrected
pair count is 50,847,530 (was 50,847,529). The corrected Artin prime count
(distinct primes) is 19,016,617 (the row count of the original CSV was
19,016,618 due to the duplicate p=7 being Artin). No displayed headline
statistic is materially affected.

## Repository layout

```
code/      prime_sieve_1e9.c    Segmented Eratosthenes sieve; emits the per-prime dataset
                                 Configurable limit via command-line argument.
code/      pilot_consecutive_artin.py   Global + gap-stratified contingency analysis
           pilot2_residual.py           Residue-conditioned analysis (mod 120)
           pilot3_robustness.py         Robustness: mod-840 conditioning, split-half
           verify_theorem.py            Independent verification of Theorem 1
           recompute_corrected.py       Full recomputation of the corrected CSV
paper/     consecutive_artin.tex/.pdf   The manuscript
           make_figure.py               Generates Figure 1
results/   *_log.txt, *_results.json    Raw outputs backing every number in the paper
archive/   pre-finalization/          Superseded local manuscripts (archival only)
```

## Reproducing the results

### Dependencies

- C compiler and GMP library (`libgmp-dev` on Debian/Ubuntu)
- Python 3 with SymPy (for theorem verification)
- Matplotlib (for figure generation)
- pdflatex with amsart (for manuscript compilation)

### 1. Build and run the sieve

```bash
gcc -O3 -o prime_sieve_1e9 code/prime_sieve_1e9.c -lm -lgmp
./prime_sieve_1e9 > data_1e9.csv                    # default: 10^9
./prime_sieve_1e9 1000000 > data_1e6.csv             # smaller test run
```

The CSV is ~1.8 GB for the full 10⁹ run. The computation is fully
deterministic, so the file is exactly reproducible from source.

### 2. Run the analysis

All scripts accept input CSV and output directory as command-line arguments,
defaulting to repository-relative paths:

```bash
# Full analysis (requires data_1e9.csv in repo root):
python3 code/pilot_consecutive_artin.py
python3 code/pilot2_residual.py
python3 code/pilot3_robustness.py

# With explicit paths:
python3 code/pilot_consecutive_artin.py data_1e9.csv results/

# Theorem verification (uses sympy, no CSV needed):
python3 code/verify_theorem.py

# Full corrected recomputation (single pass, all statistics):
python3 code/recompute_corrected.py data_1e9.csv results/
```

Reference outputs from the corrected runs are supplied under `results/` and in
the corrected public repository. The massive raw CSV is excluded.

### 3. Generate Figure 1

```bash
python3 paper/make_figure.py                          # uses results/pilot_results.json
python3 paper/make_figure.py results/pilot_results.json paper/
```

### 4. Build the paper

```bash
cd paper && pdflatex consecutive_artin.tex && pdflatex consecutive_artin.tex
```

## Sanity check

The dataset contains **19,016,617** distinct Artin primes (proportion **0.373993**),
matching Artin's constant `C ≈ 0.3739558` to four decimal places. Agreement with
a conjectural density is a sanity check, not a verification of every indicator.

## Citation

```bibtex
@misc{Bald_ConsecutiveArtin,
  author = {Josh Bald},
  title  = {Correlations between primitive root statuses of consecutive primes},
  year   = {2026},
  note   = {Preprint}
}
```

## License

Code released under the MIT License (see `LICENSE`). The manuscript text and
figures are © the author, all rights reserved.


## Machine-checked proof (`lean/`)

Theorem 1 (the exclusion law for gaps `g ≡ 20 (mod 40)`) and its `g ≡ 0 (mod 40)`
companion are formalized in Lean 4 against Mathlib. The headline statements are
expressed in terms of Mathlib's genuine `legendreSym`, not a bespoke definition:

- `legendreSym_flip_of_shift_twenty` — for primes `p, p' ∉ {2,5}` with
  `p' ≡ p + 20 (mod 40)`, `(10|p') = -(10|p)`.
- `not_both_artin` — such a pair cannot both be Artin primes for base 10.
- `chi10_eq_legendreSym` — bridges the residue-class character to `legendreSym`
  using the second supplementary law and quadratic reciprocity (`5 ≡ 1 mod 4`).

`lean/gate.sh` checks that the build succeeds, that no `sorry`, `admit`, `axiom`,
or `native_decide` appears, and that every theorem depends only on Lean's three
standard axioms. Expected output: `PASS (19 theorems, standard axioms only)`.

Scope limits are stated in `lean/README_LEAN.md`: nothing empirical is
formalized (not `δ = -0.01414`, the z-scores, the channel decompositions, or any
conjecture), primality of `p + g` is a hypothesis rather than a conclusion, and
Papers 2–7 are untouched. Build instructions: `lean/BUILD.md`.

## Verification and provenance

Read `FINAL_STATUS.md` for completed checks, limitations, and authoritative paths.
The full CSV is outside this folder at `../data_1e9.csv`; pass that path explicitly
or generate a fresh CSV here. This folder uses `code/`, not `analysis/` or `sieve/`.
The supplementary `analyze_1e9.py` studies loneliness and is not the source of the
consecutive-pair table. Its percentile outputs use a deterministic reservoir sample.
