import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Matrix.Basic
import Def.Algebra.MvPolynomial.RegularFunction
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

@[simp]
theorem Jacobian_apply (F : RegularFunction k σ τ) (j : τ) (i : σ) :
    F.Jacobian j i = MvPolynomial.pderiv i (F j) :=
  rfl

end RegularFunction
end MvPolynomial
end
