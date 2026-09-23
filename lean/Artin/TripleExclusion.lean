/-
Copyright (c) 2026 J. Bald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bald
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic
import Artin.PrimitiveRootBridge

set_option linter.style.header false

/-!
# Triple exclusion law for same-prime Artin status

Formalization of **Theorem 2** of Paper 3 ("Cross-base correlations of Artin
status at a single prime"):

> Let `a, b, c` be non-square positive integers with `sqf(c) = sqf(ab)`, and let
> `p ∤ 2abc` be prime. Then `p` is not simultaneously Artin base `a`, Artin base
> `b`, and Artin base `c`.

The paper's proof is three lines: complete multiplicativity of the Legendre
symbol gives `χ_a(p) χ_b(p) = χ_{ab}(p) = χ_c(p)` (the last step because `ab`
and `c` differ by a square factor), and being an Artin prime for a base forces
that base to be a quadratic non-residue, so all three symbols would be `-1`,
giving `(-1)(-1) = -1`.

## Encoding of the hypotheses

* **`sqf(c) = sqf(ab)`** is expressed as `c * s ^ 2 = a * b * t ^ 2` with
  `s, t ≠ 0`.  This is equivalent to equality of squarefree parts and avoids
  needing a `sqf` function; the witnesses are immediate in practice, e.g.
  `(a,b,c) = (2,5,40)` has `40 * 1 ^ 2 = 2 * 5 * 2 ^ 2`.
* **"Artin base `a` forces `χ_a(p) = -1`"** is proved from the definition of a
  primitive root via `Artin/PrimitiveRootBridge.lean`
  (`legendreSym_eq_neg_one_of_isPrimitiveRoot`), and composed into this file
  below (`not_all_three_nonresidue_of_primitiveRoot`,
  `legendreSym_third_eq_one_of_primitiveRoot`). The
  `legendreSym p a = -1`-hypothesis theorems remain as the character-parity
  core — they hold for the genuine `legendreSym` independent of *how* the `-1`
  arose — and the `_of_primitiveRoot` variants discharge that hypothesis from
  an actual `IsPrimitiveRoot` fact, closing the gap end-to-end. See
  `README_LEAN.md`.

The theorem below is therefore the **character-parity core** of Theorem 2: it is
the step that does the actual work, and it holds for the genuine `legendreSym`.
-/

namespace ArtinExclusion

open ZMod

variable {p : ℕ} [Fact p.Prime]

/-- If `x` is a nonzero square modulo `p`, its Legendre symbol is `1`. -/
private theorem legendreSym_sq {s : ℤ} (hs : ((s : ZMod p)) ≠ 0) :
    legendreSym p (s ^ 2) = 1 := by
  have : legendreSym p (s ^ 2) = (legendreSym p s) ^ 2 := by
    rw [sq, sq, legendreSym.mul]
  rw [this]
  rcases legendreSym.eq_one_or_neg_one p hs with h | h <;> rw [h] <;> norm_num

/-- **Character-parity core of Paper 3, Theorem 2.**

If `c * s ^ 2 = a * b * t ^ 2` (that is, `sqf c = sqf (a*b)`), and the
square witnesses `s, t` do not vanish mod `p`, then the three Legendre
symbols cannot all be `-1`.

Note: hypotheses `a, b ≢ 0 (mod p)` are *not* required — Lean confirmed they are
redundant, since `legendreSym p a = -1` already forces `a ≢ 0 (mod p)`
(a vanishing base would give symbol `0`). The paper's `p ∤ 2abc` condition
is correspondingly stronger than the parity argument actually needs.

Consequently no prime is simultaneously a quadratic non-residue
witness for `a`, `b` and `c` — the obstruction behind "no prime has `2`, `5`
and `10` all as primitive roots". -/
theorem not_all_three_nonresidue
    {a b c s t : ℤ}
    (hrel : c * s ^ 2 = a * b * t ^ 2)
    (hs : ((s : ZMod p)) ≠ 0) (ht : ((t : ZMod p)) ≠ 0) :
    ¬ (legendreSym p a = -1 ∧ legendreSym p b = -1 ∧ legendreSym p c = -1) := by
  rintro ⟨hA, hB, hC⟩
  -- take Legendre symbols of both sides of the relation
  have h := congrArg (fun z : ℤ => legendreSym p z) hrel
  simp only [legendreSym.mul, legendreSym_sq hs, legendreSym_sq ht, mul_one] at h
  -- h : legendreSym p c = legendreSym p a * legendreSym p b
  rw [hA, hB, hC] at h
  norm_num at h

/-- **Triple exclusion, in the paper's shape.**  With `χ_a(p) = χ_b(p) = -1`
(both `a` and `b` non-residues, as Artin status for each forces), the third
base `c` in the multiplicative triple is a quadratic *residue*, hence cannot be
a primitive root: `legendreSym p c = 1`. -/
theorem legendreSym_third_eq_one
    {a b c s t : ℤ}
    (hrel : c * s ^ 2 = a * b * t ^ 2)
    (hs : ((s : ZMod p)) ≠ 0) (ht : ((t : ZMod p)) ≠ 0)
    (hA : legendreSym p a = -1) (hB : legendreSym p b = -1) :
    legendreSym p c = 1 := by
  have h := congrArg (fun z : ℤ => legendreSym p z) hrel
  simp only [legendreSym.mul, legendreSym_sq hs, legendreSym_sq ht, mul_one] at h
  rw [hA, hB] at h
  simp only [neg_mul, neg_neg, one_mul] at h
  exact h

/-- Specialisation to the paper's headline example `(2, 5, 10)`: for **any**
prime `p`, the bases `2`, `5`, `10` cannot all three be quadratic non-residues,
hence cannot all three be primitive roots. Here `10 * 1 ^ 2 = 2 * 5 * 1 ^ 2`. -/
theorem not_all_three_nonresidue_two_five_ten :
    ¬ (legendreSym p 2 = -1 ∧ legendreSym p 5 = -1 ∧ legendreSym p 10 = -1) := by
  refine not_all_three_nonresidue (s := 1) (t := 1) (by ring) ?_ ?_
  · simp
  · simp

/-- **End-to-end composition, hypothesis-free.** Same statement as
`not_all_three_nonresidue`, but with "Artin base `a`" / "Artin base `b`"
expressed as actual `IsPrimitiveRoot` facts (`a`, `b` generate the full unit
group mod `p`) rather than as bare `legendreSym = -1` hypotheses. This closes
the gap `LEAN_NOTE.md` used to flag: the translation "primitive root ⇒
non-residue" is no longer assumed anywhere in the chain from primitive root to
triple exclusion. -/
theorem not_all_three_nonresidue_of_primitiveRoot
    (hp2 : p ≠ 2)
    {a b c s t : ℤ}
    (hrel : c * s ^ 2 = a * b * t ^ 2)
    (hs : ((s : ZMod p)) ≠ 0) (ht : ((t : ZMod p)) ≠ 0)
    (ha : IsPrimitiveRoot ((a : ZMod p)) (p - 1))
    (hb : IsPrimitiveRoot ((b : ZMod p)) (p - 1))
    (hC : legendreSym p c = -1) :
    False :=
  not_all_three_nonresidue hrel hs ht
    ⟨legendreSym_eq_neg_one_of_isPrimitiveRoot hp2 ha,
     legendreSym_eq_neg_one_of_isPrimitiveRoot hp2 hb, hC⟩

/-- Same composition for `legendreSym_third_eq_one`: if `a` and `b` are both
primitive roots mod `p` (hence both non-residues) and `c` completes the
multiplicative triple, then `c` is forced to be a residue — with "`a`, `b`
Artin" expressed as genuine `IsPrimitiveRoot` facts, not assumed
non-residues. -/
theorem legendreSym_third_eq_one_of_primitiveRoot
    (hp2 : p ≠ 2)
    {a b c s t : ℤ}
    (hrel : c * s ^ 2 = a * b * t ^ 2)
    (hs : ((s : ZMod p)) ≠ 0) (ht : ((t : ZMod p)) ≠ 0)
    (ha : IsPrimitiveRoot ((a : ZMod p)) (p - 1))
    (hb : IsPrimitiveRoot ((b : ZMod p)) (p - 1)) :
    legendreSym p c = 1 :=
  legendreSym_third_eq_one hrel hs ht
    (legendreSym_eq_neg_one_of_isPrimitiveRoot hp2 ha)
    (legendreSym_eq_neg_one_of_isPrimitiveRoot hp2 hb)

end ArtinExclusion
