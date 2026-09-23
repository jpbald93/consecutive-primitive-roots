/-
Copyright (c) 2026 J. Bald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bald
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Paper 2 — refutation of the twin-prime claim, and the corrected count

Paper 2 ("Exclusion laws for consecutive Artin primes in arbitrary bases") was
**BLOCKed** by the 2026-09-10 audit on two counts that this file settles
mechanically.

## 1. The `g = 2` twin-prime claim is false

Paper 2, p.13 ("Relation to earlier work") asserts that `g = 2` is an exclusion
class exactly when `f | 12`, "so `a ≡ 3, 12, 27, …` are the twin-prime cases
covered by our law". An exclusion class for base `a` means (Definition 6) that
**no** pair of primes `p, q` with `q - p ≡ g (mod f)` can both be Artin base `a`.

`refutation_gap_two_base_three` shows `3` is a primitive root modulo both `5`
and `7` — a twin pair at gap `2`. So `g = 2` is **not** an exclusion class for
base `3`, and the quoted sentence is false. The paper's own Table 2 lists `2` as
*preserving* for `f = 12`, contradicting its text, so this is an internal
inconsistency rather than a slip in one line.

"Primitive root" is certified here in computable form: `3 ^ k ≠ 1` for every
`k` properly dividing the group order, and `3 ^ order = 1`. For `ZMod 5` the
group order is `4` (check `k = 1, 2`); for `ZMod 7` it is `6` (check
`k = 1, 2, 3`).

## 2. Theorem 2 is missing the hypothesis `g ≢ 0 (mod d)`

Paper 2, p.2, Theorem 2 states that for prime `d ≡ 1 (mod 4)` the number of
residues `r` mod `d` with `r, r + g ≢ 0` and `χ(r) = χ(r + g) = -1` equals
`(d - 3 + 2 χ(g)) / 4`. At `g ≡ 0 (mod d)` that is false and not even an
integer: for `d = 13` it gives `2.5` where the true count is `6`.

`nmm_five` and `nmm_thirteen` record the **corrected** two-case count:

* `g ≡ 0 (mod d)` : the count is `(d - 1) / 2`;
* `g ≢ 0 (mod d)` : the count is `(d - 3 + 2 χ(g)) / 4`.

`paper_formula_fails_at_zero` states the failure as an explicit inequality.
The parts of Theorem 2 that *are* correct are also confirmed:
`nmm_five_vanishes` (base 5 has exclusion classes exactly at `g ≡ 2, 3 mod 5`)
and `nmm_thirteen_never_vanishes` (base 13 has none).

## Scope

The general-`d` statement rests on a Jacobsthal-type identity
(`∑_r χ(r) χ(r + g) = -1` for `g ≢ 0`) that is **not** in Mathlib and is not
proved here. This file gives an unconditional refutation of the twin-prime
claim plus the corrected count for concrete `d`. See `README_LEAN.md`.
-/

namespace Paper2

/-! ### 1. Refutation of the `g = 2` twin-prime claim -/

/-- `3` generates `(ZMod 5)ˣ`: `3 ^ 4 = 1` while `3 ^ 1, 3 ^ 2 ≠ 1`.
Since the group order is `4`, whose proper divisors are `1, 2`, this certifies
that `3` is a primitive root modulo `5`. -/
theorem three_primitiveRoot_five :
    (3 : ZMod 5) ^ 4 = 1 ∧ (3 : ZMod 5) ^ 1 ≠ 1 ∧ (3 : ZMod 5) ^ 2 ≠ 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-- `3` generates `(ZMod 7)ˣ`: `3 ^ 6 = 1` while `3 ^ 1, 3 ^ 2, 3 ^ 3 ≠ 1`.
The group order is `6`, with proper divisors `1, 2, 3`. -/
theorem three_primitiveRoot_seven :
    (3 : ZMod 7) ^ 6 = 1 ∧ (3 : ZMod 7) ^ 1 ≠ 1 ∧ (3 : ZMod 7) ^ 2 ≠ 1 ∧
      (3 : ZMod 7) ^ 3 ≠ 1 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The relevant group orders, so the exponents above are the full orders. -/
theorem group_orders : Fintype.card (ZMod 5)ˣ = 4 ∧ Fintype.card (ZMod 7)ˣ = 6 := by
  refine ⟨by decide, by decide⟩

/-- **Refutation of Paper 2, p.13.**  `5` and `7` are primes differing by `2`,
and `3` is a primitive root modulo both.  Therefore `g = 2` is not an exclusion
class for base `3`, contradicting the claim that `a ≡ 3` is among "the
twin-prime cases covered by our law". -/
theorem refutation_gap_two_base_three :
    Nat.Prime 5 ∧ Nat.Prime 7 ∧ 7 - 5 = 2 ∧
      ((3 : ZMod 5) ^ 4 = 1 ∧ (3 : ZMod 5) ^ 2 ≠ 1) ∧
      ((3 : ZMod 7) ^ 6 = 1 ∧ (3 : ZMod 7) ^ 3 ≠ 1 ∧ (3 : ZMod 7) ^ 2 ≠ 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ⟨by decide, by decide⟩,
    ⟨by decide, by decide, by decide⟩⟩

/-! ### 2. The corrected count in Theorem 2

`chi` is the quadratic character via Euler's criterion, which is computable, so
every statement below is discharged by `decide`. -/

/-- Quadratic character mod `d` by Euler's criterion, as an integer:
`0` at `0`, `1` if `r ^ ((d-1)/2) = 1`, else `-1`. -/
def chi (d : ℕ) [NeZero d] (r : ZMod d) : ℤ :=
  if r = 0 then 0 else if r ^ ((d - 1) / 2) = 1 then 1 else -1

/-- `N--(g)`: the number of residues `r` mod `d` with `χ(r) = χ(r + g) = -1`
(the conditions `r ≠ 0` and `r + g ≠ 0` are implied, since `χ` is `0` there). -/
def nmm (d : ℕ) [NeZero d] (g : ZMod d) : ℕ :=
  (Finset.univ.filter fun r : ZMod d => chi d r = -1 ∧ chi d (r + g) = -1).card

/-- **Corrected Theorem 2 for `d = 5`**, both cases.  At `g = 0` the count is
`(5-1)/2 = 2`; the paper's formula would give `1/2`. -/
theorem nmm_five (g : ZMod 5) :
    (g = 0 → nmm 5 g = 2) ∧ (g ≠ 0 → 4 * (nmm 5 g : ℤ) = 5 - 3 + 2 * chi 5 g) := by
  revert g; decide

/-- **Corrected Theorem 2 for `d = 13`**, both cases.  At `g = 0` the count is
`(13-1)/2 = 6`; the paper's formula would give `2.5`, not an integer. -/
theorem nmm_thirteen (g : ZMod 13) :
    (g = 0 → nmm 13 g = 6) ∧
      (g ≠ 0 → 4 * (nmm 13 g : ℤ) = 13 - 3 + 2 * chi 13 g) := by
  revert g; decide

/-- **The missing hypothesis, as an inequality.**  Paper 2's formula applied at
`g = 0` with `d = 13` gives `10`, while `4 * N--(0) = 24`. -/
theorem paper_formula_fails_at_zero :
    4 * (nmm 13 0 : ℤ) ≠ 13 - 3 + 2 * chi 13 0 := by decide

/-- Confirming what Theorem 2 gets right: for `d = 5` the count vanishes exactly
on `g ≡ 2, 3 (mod 5)` — the inadmissibility exclusion classes. -/
theorem nmm_five_vanishes (g : ZMod 5) : nmm 5 g = 0 ↔ (g = 2 ∨ g = 3) := by
  revert g; decide

/-- Also correct: for `d = 13` the count never vanishes, so base `13` admits no
inadmissibility exclusion class. -/
theorem nmm_thirteen_never_vanishes (g : ZMod 13) : nmm 13 g ≠ 0 := by
  revert g; decide

end Paper2
