import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Matrix.Basic
import Abbrev.Algebra.MvPolynomial.RegularFunction
/-!
# Regular functions between affine spaces

A *regular function* from `k^σ` to `k^τ` is a `τ`-indexed family of polynomials in
the variables `σ`, i.e. a vector valued polynomial function. This file provides
the basic API: the Jacobian matrix, composition, the identity, and evaluation at
a point.
-/


noncomputable section

namespace MvPolynomial

variable {k : Type*} [CommSemiring k]

variable {σ τ ι κ : Type*}

namespace RegularFunction

/-- The Jacobian of a vector valued polynomial function, viewed as a polynomial.

The matrix is indexed as codomain by domain, following Mathlib's matrix
convention: entry `(j, i)` is the partial derivative of the `j`-th component
with respect to the `i`-th variable. -/
noncomputable def Jacobian (F : RegularFunction k σ τ) :
    Matrix τ σ (MvPolynomial σ k) :=
  Matrix.of fun j i => MvPolynomial.pderiv i (F j)

end RegularFunction
end MvPolynomial
end
