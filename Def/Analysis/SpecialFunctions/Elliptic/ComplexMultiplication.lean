import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
/-!
# Complex multiplication of period lattices

This file defines the endomorphism ring of a complex period lattice.
-/


namespace PeriodPair

/-- The subring of complex scalars whose multiplication preserves a period lattice. -/
def endomorphismRing (L : PeriodPair) : Subring ℂ where
  carrier := {a | ∀ z ∈ L.lattice, a * z ∈ L.lattice}
  mul_mem' ha hb z hz := by
    rw [mul_assoc]
    exact ha _ (hb z hz)
  one_mem' z hz := by simpa using hz
  add_mem' ha hb z hz := by
    rw [add_mul]
    exact add_mem (ha z hz) (hb z hz)
  zero_mem' _ _ := by simp
  neg_mem' ha z hz := by
    rw [neg_mul]
    exact neg_mem (ha z hz)

end PeriodPair
