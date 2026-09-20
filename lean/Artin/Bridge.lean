/-
Copyright (c) 2026 J. Bald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bald
-/
import Artin.Exclusion

set_option linter.style.header false

/-!
# Bridge: the residue-class character equals the genuine Legendre symbol

`Artin/Exclusion.lean` proves the exclusion law for a character `chi10` defined
by residue conditions mod 8 and mod 5.  This file connects that definition to
Mathlib's `legendreSym`, so the exclusion law becomes a statement about the real
quadratic character rather than about a convenient definition.

The two ingredients are the ones the paper cites:
* `ZMod.exists_sq_eq_two_iff` — `2` is a square mod `p` iff `p % 8 ∈ {1,7}`
  (second supplementary law);
* `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one` — reciprocity for `5`,
  applicable because `5 % 4 = 1`.
-/

namespace ArtinExclusion

open ZMod

variable {p : ℕ} [Fact p.Prime]

/-- For a prime `p` and a prime `q`, `(q : ZMod p) = 0` forces `p = q`. -/
private theorem cast_prime_ne_zero {q : ℕ} (hq : q.Prime) (hne : p ≠ q) :
    ((q : ℕ) : ZMod p) ≠ 0 := by
  intro h
  exact hne ((Nat.prime_dvd_prime_iff_eq Fact.out hq).mp
    ((ZMod.natCast_eq_zero_iff q p).mp h))

/-- `(2|p) = 1` exactly on the classes `p % 8 ∈ {1,7}`. -/
theorem legendreSym_two_eq (hp2 : p ≠ 2) :
    legendreSym p 2 = if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1 := by
  have hne : ((2 : ℕ) : ZMod p) ≠ 0 := cast_prime_ne_zero Nat.prime_two hp2
  by_cases h : p % 8 = 1 ∨ p % 8 = 7
  · simp only [h, if_true]
    have : legendreSym p (2 : ℕ) = 1 :=
      (legendreSym.eq_one_iff' p hne).mpr ((ZMod.exists_sq_eq_two_iff hp2).mpr h)
    simpa using this
  · simp only [h, if_false]
    have : legendreSym p (2 : ℕ) = -1 :=
      (legendreSym.eq_neg_one_iff' p).mpr
        (fun hsq => h ((ZMod.exists_sq_eq_two_iff hp2).mp hsq))
    simpa using this

/-- `IsSquare (n : ZMod 5)` iff `n % 5 ∈ {1,4}`, **provided `5 ∤ n`**.

The hypothesis `n % 5 ≠ 0` is necessary and was initially omitted: `0` is a
square in `ZMod 5` (`0 = 0 * 0`), so without it the `→` direction is false.
Lean rejected the statement until the hypothesis was added. In the application
`n = p` is a prime `≠ 5`, so the hypothesis holds. -/
private theorem isSquare_cast_five (n : ℕ) (hn : n % 5 ≠ 0) :
    IsSquare ((n : ℕ) : ZMod 5) ↔ (n % 5 = 1 ∨ n % 5 = 4) := by
  have hcast : ((n : ℕ) : ZMod 5) = ((n % 5 : ℕ) : ZMod 5) := by
    have := ZMod.natCast_mod n 5
    exact this.symm
  have hlt : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  rw [hcast]
  -- decide each admissible residue case explicitly
  have h5 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases h5 with h | h | h | h | h
  · exact absurd h hn
  · simp only [h]
    exact ⟨fun _ => Or.inl trivial, fun _ => ⟨1, by decide⟩⟩
  · simp only [h]
    exact ⟨by decide, by omega⟩
  · simp only [h]
    exact ⟨by decide, by omega⟩
  · simp only [h]
    exact ⟨fun _ => Or.inr trivial, fun _ => ⟨2, by decide⟩⟩

/-- `(5|p) = 1` exactly on the classes `p % 5 ∈ {1,4}`, by reciprocity. -/
theorem legendreSym_five_eq (hp5 : p ≠ 5) (hp2 : p ≠ 2) :
    legendreSym p 5 = if p % 5 = 1 ∨ p % 5 = 4 then 1 else -1 := by
  have h5fact : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hne5 : ((5 : ℕ) : ZMod p) ≠ 0 := cast_prime_ne_zero (by norm_num) hp5
  -- `p` is prime and `≠ 5`, so `5 ∤ p`, giving the hypothesis of `isSquare_cast_five`
  have hpprime : Nat.Prime p := Fact.out
  have hpmod : p % 5 ≠ 0 := by
    intro h
    have h5dvd : (5 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hpprime).mp h5dvd).symm
  -- reciprocity is stated with `p := 5`, `q := p`, giving the reverse orientation
  have key : IsSquare ((5 : ℕ) : ZMod p) ↔ IsSquare ((p : ℕ) : ZMod 5) :=
    (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := p)
      (by norm_num) hp2).symm
  by_cases h : p % 5 = 1 ∨ p % 5 = 4
  · simp only [h, if_true]
    have : legendreSym p (5 : ℕ) = 1 :=
      (legendreSym.eq_one_iff' p hne5).mpr (key.mpr ((isSquare_cast_five p hpmod).mpr h))
    simpa using this
  · simp only [h, if_false]
    have : legendreSym p (5 : ℕ) = -1 :=
      (legendreSym.eq_neg_one_iff' p).mpr
        (fun hsq => h ((isSquare_cast_five p hpmod).mp (key.mp hsq)))
    simpa using this

/-- **Bridge theorem.** For a prime `p ∉ {2, 5}`, the residue-class character
`chi10` evaluated at `p mod 40` agrees with the genuine Legendre symbol
`(10 | p)`. -/
theorem chi10_eq_legendreSym (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    chi10 (p : ZMod 40) = legendreSym p 10 := by
  have h10 : legendreSym p 10 = legendreSym p 2 * legendreSym p 5 := by
    have : (10 : ℤ) = 2 * 5 := by norm_num
    rw [this, legendreSym.mul]
  rw [h10, legendreSym_two_eq hp2, legendreSym_five_eq hp5 hp2]
  have hv : ((p : ZMod 40)).val = p % 40 := ZMod.val_natCast 40 p
  have h8 : p % 40 % 8 = p % 8 := Nat.mod_mod_of_dvd p (by norm_num)
  have h5 : p % 40 % 5 = p % 5 := Nat.mod_mod_of_dvd p (by norm_num)
  simp only [chi10, chi2, chi5, hv, h8, h5]

end ArtinExclusion
