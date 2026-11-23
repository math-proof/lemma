module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Matrix.Basic
public import Def.Algebra.MvPolynomial.RegularFunction.Part3

/-!
# Regular functions between affine spaces

A *regular function* from `k^σ` to `k^τ` is a `τ`-indexed family of polynomials in
the variables `σ`, i.e. a vector valued polynomial function. This file provides
the basic API: the Jacobian matrix, composition, the identity, and evaluation at
a point.
-/

public section


noncomputable section

namespace MvPolynomial

variable {k : Type*} [CommSemiring k]

variable {σ τ ι κ : Type*}

namespace RegularFunction

/-- `aeval` is compatible with composition of regular functions. -/
theorem comp_aeval
    {σ τ ι S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (G : RegularFunction k τ ι) (F : RegularFunction k σ τ)
    (a : σ → S₁) : (G.comp F).aeval a = G.aeval (F.aeval a) := by
  ext i
  rw [aeval, comp, MvPolynomial.aeval_bind₁, ←aeval]
  rfl

end RegularFunction
end MvPolynomial
end
