/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/QuadrinomialCoefficient.lean -/


import Mathlib.Algebra.Polynomial.Coeff
import Def.Combinatorics.Enumerative.QuadrinomialCoefficient


namespace MetaMathlibExt

example : polynomialQuadrinomialCoeff 1 0 = 1 := by
  simp [polynomialQuadrinomialCoeff]

example : polynomialQuadrinomialCoeff 1 2 = 1 := by
  simp [polynomialQuadrinomialCoeff, Polynomial.coeff_one, Polynomial.coeff_X]

end MetaMathlibExt
