/-
Copyright (c) 2026 J. Bald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bald
-/
import Mathlib.Tactic

set_option linter.style.header false
set_option linter.unusedDecidableInType false

/-!
# Paper 2 rebuild — the general counting identity

The rebuilt Paper 2 replaces its broken composite-case argument with a single
elementary identity that needs **no** hypothesis on the modulus (prime or
composite conductor alike).

Fix a modulus and a "character" `chi` taking values in `{-1, 0, 1}`, with
`chi r = 0` exactly off the unit set. For a shift `g`, let

* `U g = { r : chi r ≠ 0 ∧ chi (r+g) ≠ 0 }`, `T g = |U g|`
* `A g = ∑_{r ∈ U g} chi r`, `B g = ∑_{r ∈ U g} chi (r+g)`
* `S g = ∑_r chi r * chi (r+g)`   (summed over everything; terms off `U g` vanish)
* `N g = #{ r ∈ U g : chi r = -1 ∧ chi (r+g) = -1 }`

Then

    4 * N g = T g - A g - B g + S g.

The proof is the pointwise identity
`4 * [x = -1 ∧ y = -1] = (1 - x) * (1 - y)` for `x, y ∈ {-1, 1}`, summed over
`U g`. `main_identity` below proves it for an arbitrary `Finset` and arbitrary
`ℤ`-valued functions taking values in `{-1, 1}` on that set, which is the
general form the paper needs.

**Why this matters for the paper.** Paper 2's Theorem 2 formula
`(d - 3 + 2 χ(g))/4` is this identity specialised by `A g = -χ(-g)`,
`B g = -χ(g)`, `S g = -1`, `T g = d - 2`. The step `A g = -χ(-g)` is valid only
for **prime** conductor; it fails for composite conductor (checked: it holds in
294 of 490 tested cases and fails in 196, always at composite `f`). That is
exactly why Corollary 14's composite case could not be proved the old way. The
identity below has no such restriction.
-/

namespace Paper2Rebuild

open Finset

/-! ### The identity -/

/-- Pointwise core: for `x, y ∈ {-1, 1}`, four times the indicator of
`x = -1 ∧ y = -1` equals `(1 - x) * (1 - y)`. -/
theorem four_mul_indicator {x y : ℤ} (hx : x = -1 ∨ x = 1) (hy : y = -1 ∨ y = 1) :
    4 * (if x = -1 ∧ y = -1 then (1 : ℤ) else 0) = (1 - x) * (1 - y) := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> subst hx <;> subst hy <;> norm_num

/-- **The general counting identity.**  For any finite index set `U` and any
`ℤ`-valued `f, h` taking values in `{-1, 1}` on `U`:

`4 * #{r ∈ U : f r = -1 ∧ h r = -1} = |U| - ∑ f - ∑ h + ∑ f * h`.

No primality, no modulus, no character theory — this is the engine that replaces
Paper 2's composite-case argument. -/
theorem main_identity {α : Type*} [DecidableEq α] (U : Finset α) (f h : α → ℤ)
    (hf : ∀ r ∈ U, f r = -1 ∨ f r = 1) (hh : ∀ r ∈ U, h r = -1 ∨ h r = 1) :
    4 * ((U.filter fun r => f r = -1 ∧ h r = -1).card : ℤ)
      = (U.card : ℤ) - (∑ r ∈ U, f r) - (∑ r ∈ U, h r) + (∑ r ∈ U, f r * h r) := by
  have key : 4 * ((U.filter fun r => f r = -1 ∧ h r = -1).card : ℤ)
      = ∑ r ∈ U, (1 - f r) * (1 - h r) := by
    rw [Finset.card_filter]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    exact four_mul_indicator (hf r hr) (hh r hr)
  rw [key]
  have expand : ∀ r ∈ U, (1 - f r) * (1 - h r)
      = 1 - f r - h r + f r * h r := fun r _ => by ring
  rw [Finset.sum_congr rfl expand]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- Restated in the paper's notation: with `T = |U|`, `A = ∑ f`, `B = ∑ h`,
`S = ∑ f * h`, and `N` the doubly-negative count, `4N = T - A - B + S`. -/
theorem counting_identity {α : Type*} [DecidableEq α] (U : Finset α) (f h : α → ℤ)
    (hf : ∀ r ∈ U, f r = -1 ∨ f r = 1) (hh : ∀ r ∈ U, h r = -1 ∨ h r = 1)
    (N T A B S : ℤ)
    (hN : N = ((U.filter fun r => f r = -1 ∧ h r = -1).card : ℤ))
    (hT : T = (U.card : ℤ)) (hA : A = ∑ r ∈ U, f r) (hB : B = ∑ r ∈ U, h r)
    (hS : S = ∑ r ∈ U, f r * h r) :
    4 * N = T - A - B + S := by
  subst hN hT hA hB hS
  exact main_identity U f h hf hh

end Paper2Rebuild
