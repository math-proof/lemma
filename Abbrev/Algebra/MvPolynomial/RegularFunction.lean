import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Matrix.Basic
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

variable (k σ τ) in
/-- The type of regular functions from `k^σ` to `k^τ`. -/
abbrev RegularFunction := τ → MvPolynomial σ k

end MvPolynomial
end
