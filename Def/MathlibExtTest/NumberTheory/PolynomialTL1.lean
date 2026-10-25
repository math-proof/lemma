/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PolynomialTL1.lean -/


import Def.NumberTheory.PolynomialTL1
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Theorem.MathlibExtTest.NumberTheory.PolynomialTL1


namespace MetaMathlibExt

open Polynomial

/-- A concrete family exercising the `l = 0` convention and the `l - 1`
degree shift without assuming the fields of `IsPolyTFamily`. -/
noncomputable def concreteT (l : ℕ) : Polynomial ℝ :=
  if l = 0 then 0 else X ^ (l - 1)

noncomputable def concreteS (l : ℕ) : Polynomial ℝ :=
  C 8 * X ^ l - (C 4 - X) * concreteT l -
    C 2 * X * (C 4 - X) * (concreteT l).derivative

end MetaMathlibExt
