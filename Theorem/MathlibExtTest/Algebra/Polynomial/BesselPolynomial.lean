/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/BesselPolynomial.lean -/
module

public import Theorem.Algebra.Polynomial.BesselPolynomial

public section

namespace MetaMathlibExt

example : besselPolynomial 0 = 1 := besselPolynomial_zero

example :
    besselPolynomial 2 =
      Polynomial.C 1 + Polynomial.C 3 * Polynomial.X +
        Polynomial.C 3 * Polynomial.X ^ 2 :=
  besselPolynomial_two

end MetaMathlibExt
