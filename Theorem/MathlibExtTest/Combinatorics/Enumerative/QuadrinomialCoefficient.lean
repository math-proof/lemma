/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/QuadrinomialCoefficient.lean -/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Def.Combinatorics.Enumerative.QuadrinomialCoefficient

public section

namespace MetaMathlibExt

example : polynomialQuadrinomialCoeff 1 0 = 1 := by
  simp [polynomialQuadrinomialCoeff]

example : polynomialQuadrinomialCoeff 1 2 = 1 := by
  simp [polynomialQuadrinomialCoeff, Polynomial.coeff_one, Polynomial.coeff_X]

end MetaMathlibExt
