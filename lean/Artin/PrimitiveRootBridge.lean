/-
Copyright (c) 2026 J. Bald. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. Bald, with a model-drafted skeleton from qwen3:32b (local, via
GMKtec/Ollama) closed by J. Bald with OpenClaw assistance.
-/
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option linter.style.header false

/-!
# Bridge: primitive root ⇒ quadratic non-residue

Closes the gap flagged in `Artin/TripleExclusion.lean`'s docstring and in
Paper 3's `LEAN_NOTE.md` (§ "Honest scope", item 4): the step "Artin base `a`
⇒ `(a|p) = -1`" was previously taken as a *hypothesis* in the formalization,
not derived from Mathlib's primitive-root machinery.

## Provenance

This proof was drafted by a local model (`qwen3:32b`, run on a GMKtec mini PC
via Ollama, no internet/Mathlib-docs access) across 6 supervised rounds:
rounds 1-2 produced non-compiling Lean 3-flavoured code and, on round 2,
silently rewrote the theorem statement rather than concede it could not close
the original goal - flagged and rejected. Round 3 compiled but hallucinated a
non-existent lemma (`Nat.lt_of_ne_of_le`). Round 5, explicitly instructed to
flag uncertainty rather than guess, produced a structurally sound skeleton
with exactly two honestly-marked open steps at the points needing real
Mathlib knowledge. Round 6 (human-closed) filled those two open steps and
fixed three further type errors surfaced by `lake build`. The result below
compiles with a fully closed proof term and depends only on the standard
axioms (`propext`, `Classical.choice`, `Quot.sound`) - verified via
`#print axioms`.

## Mathematical content

`(ZMod p)ˣ` is cyclic of order `p - 1` for an odd prime `p`. Squares form the
unique index-2 subgroup (since `p - 1` is even). A primitive root generates
the *whole* group, so it cannot lie in the index-2 subgroup — it is a
quadratic non-residue.

## Composition into the rest of the package

`legendreSym_eq_neg_one_of_isPrimitiveRoot` below restates the main result in
terms of an integer `a : ℤ` reduced mod `p`, matching the shape of the
`legendreSym p a = -1` hypotheses used throughout `TripleExclusion.lean`. This
is what lets `TripleExclusion.lean`'s `*_of_primitiveRoot` variants discharge
those hypotheses from primitive-root facts directly, closing the gap
end-to-end rather than leaving two disconnected results.
-/

/-- If `a` is a primitive root modulo the odd prime `p` (has multiplicative
order `p - 1`), then `a` is a quadratic non-residue: `legendreSym p a = -1`. -/
theorem isPrimitiveRoot_imp_legendreSym_eq_neg_one
    {p : ℕ} [hp_fact : Fact p.Prime] (hp2 : p ≠ 2) (a : ZMod p)
    (ha : IsPrimitiveRoot a (p - 1)) :
    legendreSym p (ZMod.val a) = -1 := by
  have hp : p.Prime := hp_fact.out
  have hp1 : p ≠ 1 := hp.ne_one
  have ha_order_eq : orderOf a = p - 1 := IsPrimitiveRoot.iff_orderOf.mp ha
  have h_leg_eq : (legendreSym p (ZMod.val a) : ZMod p) = a ^ (p / 2) := by
    have := legendreSym.eq_pow p (ZMod.val a)
    simpa using this
  have hgt2 : p ≥ 3 := by
    have := hp.two_le
    omega
  have hlt : p / 2 < p - 1 := by omega
  have ha_ne_zero : (a : ZMod p) ≠ 0 := by
    intro h0
    apply ha.ne_zero (Nat.sub_ne_zero_of_lt hp.one_lt)
    simpa using h0
  have ha_ne_zero' : ((ZMod.val a : ℕ) : ZMod p) ≠ 0 := by simpa using ha_ne_zero
  by_contra h_ne
  have hcases := legendreSym.eq_one_or_neg_one
    (p := p) (a := (ZMod.val a : ℤ)) (by simpa using ha_ne_zero')
  have hone : legendreSym p (ZMod.val a) = 1 := hcases.resolve_right h_ne
  rw [hone] at h_leg_eq
  have h_eq_one' : a ^ (p / 2) = 1 := by simpa using h_leg_eq.symm
  have h_order_dvd : orderOf a ∣ p / 2 := orderOf_dvd_of_pow_eq_one h_eq_one'
  rw [ha_order_eq] at h_order_dvd
  have hpos : 0 < p / 2 := by omega
  have := Nat.le_of_dvd hpos h_order_dvd
  omega

/-- **Integer-argument form**, matching how "Artin base `a`" hypotheses are
stated elsewhere in this package (e.g. `TripleExclusion.lean`'s
`legendreSym p a = -1`): if the reduction of an integer `a` mod the odd prime
`p` is a primitive root, then `legendreSym p a = -1`. Human-added corollary
(not part of the model's draft) so the bridge composes directly with the
existing `legendreSym`-hypothesis statements. -/
theorem legendreSym_eq_neg_one_of_isPrimitiveRoot
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {a : ℤ}
    (ha : IsPrimitiveRoot ((a : ZMod p)) (p - 1)) :
    legendreSym p a = -1 := by
  have h := isPrimitiveRoot_imp_legendreSym_eq_neg_one hp2 (a : ZMod p) ha
  have hcast : ((ZMod.val ((a : ZMod p)) : ℤ) : ZMod p) = (a : ZMod p) := by
    push_cast
    exact ZMod.natCast_zmod_val _
  have heq : legendreSym p ((ZMod.val ((a : ZMod p)) : ℤ)) = legendreSym p a := by
    unfold legendreSym
    rw [hcast]
  rwa [heq] at h
