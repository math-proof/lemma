/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/ShanksCubicPolynomial.lean -/


import sympy.atlas.Algebra.Polynomial.ShanksCubicPolynomial
import Mathlib.Algebra.Polynomial.Coeff

namespace MetaMathlibExt

example : (shanksCubicPolynomial (2 : ℤ)).coeff 3 = 1 := by
  simp [shanksCubicPolynomial, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_one]

example : (shanksCubicPolynomial (2 : ℤ)).coeff 2 = -2 := by
  simp [shanksCubicPolynomial, Polynomial.coeff_X_pow, Polynomial.coeff_X,
    Polynomial.coeff_one]

end MetaMathlibExt
