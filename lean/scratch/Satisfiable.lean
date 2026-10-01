import Artin

/-! Satisfiability certificates (outside the library; not imported by it).
For every theorem with hypotheses: a Lean-checked example showing those hypotheses can all be met
simultaneously by concrete values. Theorems whose conclusion is `False` assert that their hypotheses
are jointly impossible; for those we certify that every hypothesis but the last is satisfiable,
so the impossibility is not caused by a trivially inconsistent subset. -/

set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false

-- hypotheses of ArtinExclusion.cast_prime_ne_zero are satisfiable
example : ∃ (p : ℕ) (_ : Fact p.Prime) (q : ℕ) (hq : q.Prime) (hne : p ≠ q), True :=
  ⟨13, ⟨by norm_num⟩, 7, by norm_num, by decide, trivial⟩

-- hypotheses of ArtinExclusion.legendreSym_two_eq are satisfiable
example : ∃ (p : ℕ) (_ : Fact p.Prime) (hp2 : p ≠ 2), True :=
by
  refine ⟨13, ⟨by norm_num⟩, by decide, trivial⟩

-- hypotheses of ArtinExclusion.isSquare_cast_five are satisfiable
example : ∃ (n : ℕ) (hn : n % 5 ≠ 0), True :=
by
  refine ⟨1, by decide, trivial⟩

-- hypotheses of ArtinExclusion.legendreSym_five_eq are satisfiable
example : ∃ (p : ℕ) (_ : Fact p.Prime) (hp5 : p ≠ 5) (hp2 : p ≠ 2), True :=
by
  refine ⟨7, ⟨by norm_num⟩, by decide, by decide, trivial⟩

-- hypotheses of ArtinExclusion.chi10_eq_legendreSym are satisfiable
example : ∃ (p : ℕ) (_ : Fact p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5), True :=
by
  refine ⟨7, ⟨by norm_num⟩, by decide, by decide, trivial⟩

-- hypotheses of ArtinExclusion.chi10_shift_of_gap are satisfiable
example : ∃ (r g : ZMod 40) (hr : IsUnit r) (hg : g = 20), True :=
  ⟨1, 20, isUnit_one, rfl, trivial⟩

-- hypotheses of ArtinExclusion.legendreSym_flip_of_shift_twenty are satisfiable
example : ∃ (p p' : ℕ) (_ : Fact p.Prime) (_ : Fact p'.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hq2 : p' ≠ 2) (hq5 : p' ≠ 5) (hshift : (p' : ZMod 40) = (p : ZMod 40) + 20)
    (hunit : IsUnit ((p : ZMod 40))), True :=
  ⟨3, 23, ⟨by norm_num⟩, ⟨by norm_num⟩, by decide, by decide, by decide, by decide, by decide,
    isUnit_iff_exists_inv.mpr ⟨27, by decide⟩, trivial⟩

-- hypotheses of ArtinExclusion.not_both_artin are satisfiable
example : ∃ (p p' : ℕ) (_ : Fact p.Prime) (_ : Fact p'.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hq2 : p' ≠ 2) (hq5 : p' ≠ 5) (hshift : (p' : ZMod 40) = (p : ZMod 40) + 20)
    (hunit : IsUnit ((p : ZMod 40))), True :=
  ⟨3, 23, ⟨by norm_num⟩, ⟨by norm_num⟩, by decide, by decide, by decide, by decide, by decide,
    isUnit_iff_exists_inv.mpr ⟨27, by decide⟩, trivial⟩

/-- `2` is a primitive root modulo `5` (used by the witnesses below). -/
theorem two_isPrimitiveRoot_five : IsPrimitiveRoot (2 : ZMod 5) (5 - 1) := by
  show IsPrimitiveRoot (2 : ZMod 5) 4
  refine IsPrimitiveRoot.mk_of_lt _ (by norm_num) (by decide) ?_
  intro l h0 hl
  interval_cases l <;> decide

theorem two_isPrimitiveRoot_five_int : IsPrimitiveRoot (((2 : ℤ) : ZMod 5)) (5 - 1) := by
  simpa using two_isPrimitiveRoot_five

-- hypotheses of isPrimitiveRoot_imp_legendreSym_eq_neg_one are satisfiable
example : ∃ (p : ℕ) (_ : Fact p.Prime) (hp2 : p ≠ 2) (a : ZMod p)
    (ha : IsPrimitiveRoot a (p - 1)), True :=
  ⟨5, ⟨by norm_num⟩, by decide, 2, two_isPrimitiveRoot_five, trivial⟩

-- hypotheses of legendreSym_eq_neg_one_of_isPrimitiveRoot are satisfiable
example : ∃ (p : ℕ) (_ : Fact p.Prime) (hp2 : p ≠ 2) (a : ℤ)
    (ha : IsPrimitiveRoot ((a : ZMod p)) (p - 1)), True :=
  ⟨5, ⟨by norm_num⟩, by decide, 2, two_isPrimitiveRoot_five_int, trivial⟩

-- hypotheses of ArtinExclusion.not_all_three_nonresidue are satisfiable
example : ∃ (p : ℕ) (_ : Fact p.Prime) (a b c s t : ℤ) (hrel : c * s ^ 2 = a * b * t ^ 2)
    (hs : ((s : ZMod p)) ≠ 0) (ht : ((t : ZMod p)) ≠ 0), True :=
  ⟨7, ⟨by norm_num⟩, 2, 5, 10, 1, 1, by norm_num, by decide, by decide, trivial⟩

-- hypotheses of ArtinExclusion.legendreSym_third_eq_one are satisfiable
example : ∃ (p : ℕ) (_ : Fact p.Prime) (a b c s t : ℤ) (hrel : c * s ^ 2 = a * b * t ^ 2)
    (hs : ((s : ZMod p)) ≠ 0) (ht : ((t : ZMod p)) ≠ 0)
    (hA : legendreSym p a = -1) (hB : legendreSym p b = -1), True :=
by
  refine ⟨5, ⟨by norm_num⟩, 2, 2, 1, 2, 1, by norm_num, by decide, by decide, ?_, ?_, trivial⟩ <;>
    exact @legendreSym_eq_neg_one_of_isPrimitiveRoot 5 ⟨by norm_num⟩ (by decide) 2 two_isPrimitiveRoot_five_int

-- hypotheses of ArtinExclusion.not_all_three_nonresidue_two_five_ten are satisfiable
example : ∃ (p : ℕ) (_ : Fact p.Prime), True :=
  ⟨5, ⟨by norm_num⟩, trivial⟩

-- hypotheses of ArtinExclusion.not_all_three_nonresidue_of_primitiveRoot are satisfiable
-- (conclusion is False: every hypothesis but the last, `hC`, is satisfied)
example : ∃ (p : ℕ) (_ : Fact p.Prime) (hp2 : p ≠ 2) (a b c s t : ℤ)
    (hrel : c * s ^ 2 = a * b * t ^ 2)
    (hs : ((s : ZMod p)) ≠ 0) (ht : ((t : ZMod p)) ≠ 0)
    (ha : IsPrimitiveRoot ((a : ZMod p)) (p - 1))
    (hb : IsPrimitiveRoot ((b : ZMod p)) (p - 1)), True :=
  ⟨5, ⟨by norm_num⟩, by decide, 2, 2, 1, 2, 1, by norm_num, by decide, by decide,
    two_isPrimitiveRoot_five_int, two_isPrimitiveRoot_five_int, trivial⟩

-- hypotheses of ArtinExclusion.legendreSym_third_eq_one_of_primitiveRoot are satisfiable
example : ∃ (p : ℕ) (_ : Fact p.Prime) (hp2 : p ≠ 2) (a b c s t : ℤ)
    (hrel : c * s ^ 2 = a * b * t ^ 2)
    (hs : ((s : ZMod p)) ≠ 0) (ht : ((t : ZMod p)) ≠ 0)
    (ha : IsPrimitiveRoot ((a : ZMod p)) (p - 1))
    (hb : IsPrimitiveRoot ((b : ZMod p)) (p - 1)), True :=
  ⟨5, ⟨by norm_num⟩, by decide, 2, 2, 1, 2, 1, by norm_num, by decide, by decide,
    two_isPrimitiveRoot_five_int, two_isPrimitiveRoot_five_int, trivial⟩

-- hypotheses of Paper2Rebuild.four_mul_indicator are satisfiable
example : ∃ (x y : ℤ) (hx : x = -1 ∨ x = 1) (hy : y = -1 ∨ y = 1), True :=
  ⟨1, -1, Or.inr rfl, Or.inl rfl, trivial⟩

-- hypotheses of Paper2Rebuild.main_identity are satisfiable
example : ∃ (U : Finset ℕ) (f h : ℕ → ℤ) (hf : ∀ r ∈ U, f r = -1 ∨ f r = 1)
    (hh : ∀ r ∈ U, h r = -1 ∨ h r = 1), True :=
  ⟨{0, 1}, fun _ => 1, fun _ => -1, fun _ _ => Or.inr rfl, fun _ _ => Or.inl rfl, trivial⟩

-- hypotheses of Paper2Rebuild.counting_identity are satisfiable
example : ∃ (U : Finset ℕ) (f h : ℕ → ℤ) (hf : ∀ r ∈ U, f r = -1 ∨ f r = 1)
    (hh : ∀ r ∈ U, h r = -1 ∨ h r = 1) (N T A B S : ℤ)
    (hN : N = ((U.filter fun r => f r = -1 ∧ h r = -1).card : ℤ))
    (hT : T = (U.card : ℤ)) (hA : A = ∑ r ∈ U, f r) (hB : B = ∑ r ∈ U, h r)
    (hS : S = ∑ r ∈ U, f r * h r), True :=
  ⟨{0, 1}, fun _ => 1, fun _ => -1, fun _ _ => Or.inr rfl, fun _ _ => Or.inl rfl,
    _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, trivial⟩
