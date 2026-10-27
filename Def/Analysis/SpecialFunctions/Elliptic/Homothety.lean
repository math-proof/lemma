import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
open scoped Pointwise

/-!
# Homothetic complex period lattices

Two period lattices are homothetic when one is a nonzero complex scaling of the other.
-/


namespace PeriodPair

/-- Two period pairs are homothetic when their lattices differ by a nonzero scaling. -/
def IsHomothetic (L L' : PeriodPair) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ (L'.lattice : Set ℂ) = c • (L.lattice : Set ℂ)

end PeriodPair
