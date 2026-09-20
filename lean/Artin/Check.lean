/-
Axiom audit. Every non-private declaration in this development is listed
below; `gate.sh` requires each to report only Lean's three standard axioms
(propext, Classical.choice, Quot.sound), and fails if the number of audit
lines drops. Private helper lemmas (`cast_prime_ne_zero`,
`isSquare_cast_five`) are inaccessible from this module by construction and
are covered transitively by the theorems that use them.
-/
import Artin.Exclusion
import Artin.Bridge

#print axioms ArtinExclusion.chi2
#print axioms ArtinExclusion.chi5
#print axioms ArtinExclusion.chi10
#print axioms ArtinExclusion.chi10_ne_zero
#print axioms ArtinExclusion.chi10_shift_twenty
#print axioms ArtinExclusion.chi10_shift_zero
#print axioms ArtinExclusion.not_both_nonresidue
#print axioms ArtinExclusion.chi10_shift_of_gap
#print axioms ArtinExclusion.legendreSym_two_eq
#print axioms ArtinExclusion.legendreSym_five_eq
#print axioms ArtinExclusion.chi10_eq_legendreSym
