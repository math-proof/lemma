import Mathlib.Data.Finsupp.Basic
import Def.AlgebraicGeometry.CurveDivisor


namespace CurveDivisor

variable {C : Type*}

@[simp]
theorem coeff_single (P : C) (n : ℤ) :
    coeff (Finsupp.single P n) P = n := by
  classical
  simp [coeff]

end CurveDivisor
