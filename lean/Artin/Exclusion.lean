/-
Copyright (c) 2026 J. Bald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bald
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exclusion law for consecutive Artin primes, base 10

Formalization of Theorem 1 of "Correlations between primitive root statuses of
consecutive primes":

> Let `p` and `p' = p + g` be primes with `p, p' > 5` and `g > 0`,
> `g ≡ 20 (mod 40)`. Then `(10 | p') = -(10 | p)`. In particular `10` is a
> quadratic residue modulo exactly one of `p, p'`, so at most one of them is an
> Artin prime for base `10`.

The proof in the paper factors `(10|p) = (2|p)(5|p)`, notes that `(2|p)` depends
only on `p % 8` and `(5|p) = (p|5)` depends only on `p % 5` (quadratic
reciprocity, `5 ≡ 1 mod 4`), and observes that adding `20` shifts `p` by `4`
mod `8` — flipping `(2|p)` — and by `0` mod `5` — preserving `(5|p)`.

This file formalizes the **arithmetic core**: the character defined by those two
residue conditions flips under a shift of `20` on every unit class of
`ZMod 40`, and consequently two such classes cannot both be non-residue
classes. See `README.md` for exactly what is and is not covered.
-/

namespace ArtinExclusion

/-- `chi2 r = 1` iff `r % 8 ∈ {1, 7}`: the value of the Legendre symbol `(2|p)`
for an odd prime `p` with `p % 40 = r`, by the second supplementary law. -/
def chi2 (r : ZMod 40) : ℤ :=
  if r.val % 8 = 1 ∨ r.val % 8 = 7 then 1 else -1

/-- `chi5 r = 1` iff `r % 5 ∈ {1, 4}`: the value of `(5|p) = (p|5)` for a prime
`p ≠ 5` with `p % 40 = r`, by quadratic reciprocity (`5 ≡ 1 mod 4`). -/
def chi5 (r : ZMod 40) : ℤ :=
  if r.val % 5 = 1 ∨ r.val % 5 = 4 then 1 else -1

/-- The combined character `(10|p) = (2|p)(5|p)` as a function of `p mod 40`. -/
def chi10 (r : ZMod 40) : ℤ := chi2 r * chi5 r

/-- `chi10` only ever takes the values `±1`. -/
theorem chi10_ne_zero : ∀ r : ZMod 40, chi10 r = 1 ∨ chi10 r = -1 := by decide

/-- **Arithmetic core of Theorem 1.** On every unit class of `ZMod 40`, shifting
by `20` flips the combined character. This is the finite verification the paper
performs by hand over the 16 reduced residue classes. -/
theorem chi10_shift_twenty : ∀ r : ZMod 40, IsUnit r → chi10 (r + 20) = - chi10 r := by
  decide

/-- **Companion (gaps `≡ 0 mod 40`).** Shifting by `0` in `ZMod 40` preserves the
character; this underlies the paper's corollary that gaps divisible by `40`
preserve quadratic-residue status. -/
theorem chi10_shift_zero : ∀ r : ZMod 40, chi10 (r + 40) = chi10 r := by decide

/-- **Exclusion.** Two unit classes `20` apart cannot both be non-residue
classes for base `10`. Since being an Artin prime for base `10` requires
`(10|p) = -1`, at most one of the two primes can be an Artin prime. -/
theorem not_both_nonresidue :
    ∀ r : ZMod 40, IsUnit r → ¬ (chi10 r = -1 ∧ chi10 (r + 20) = -1) := by
  decide

/-- Restated with the shift written as an arbitrary gap `g ≡ 20 (mod 40)`:
the character at `r + g` is the negation of the character at `r`. -/
theorem chi10_shift_of_gap (r g : ZMod 40) (hr : IsUnit r) (hg : g = 20) :
    chi10 (r + g) = - chi10 r := by
  subst hg
  exact chi10_shift_twenty r hr

end ArtinExclusion
