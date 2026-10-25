import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Matrix.Basic
import Theorem.Algebra.MvPolynomial.RegularFunction.Part2
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

/-- The evaluation of a regular function `f` over `k` at some point `a`
with coordinates in some algebra over `k`. -/
noncomputable def aeval {σ τ : Type*} {S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (F : RegularFunction k σ τ) : (σ → S₁) → τ → S₁ :=
  fun a t ↦ MvPolynomial.aeval a (F t)

end RegularFunction
end MvPolynomial
end
