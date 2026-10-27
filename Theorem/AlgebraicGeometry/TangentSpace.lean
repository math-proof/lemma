import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Basic
import Def.AlgebraicGeometry.TangentSpace
set_option autoImplicit false

/-! # Translated tangent spaces (ATLAS ArithmeticGeometry Definition 17.1)

This module formalizes translated tangent vectors at a point `P`:
the total derivative of a polynomial along a direction `v`,
its linearization, and the tangent spaces of a hypersurface and of an ideal.
-/


noncomputable section

namespace MvPolynomial

variable {k : Type*} [Field k] {n : Nat}

/-- The linear map evaluates as the total derivative. -/
@[simp]
theorem totalDerivativeAtLin_apply (f : MvPolynomial (Fin n) k) (P : Fin n → k)
    (v : Fin n → k) :
    totalDerivativeAtLin f P v = totalDerivativeAt f P v :=
  rfl

/-- Membership in the hypersurface tangent space is vanishing of the total derivative. -/
@[simp]
theorem mem_tangentSpacePoly (f : MvPolynomial (Fin n) k) (P : Fin n → k)
    (v : Fin n → k) :
    v ∈ tangentSpacePoly f P ↔ totalDerivativeAt f P v = 0 :=
  LinearMap.mem_ker

/-- Membership in the ideal tangent space is simultaneous vanishing on all of `I`. -/
theorem mem_tangentSpaceIdeal (I : Ideal (MvPolynomial (Fin n) k)) (P : Fin n → k)
    (v : Fin n → k) :
    v ∈ tangentSpaceIdeal I P ↔ ∀ f ∈ I, totalDerivativeAt f P v = 0 := by
  simp [tangentSpaceIdeal, mem_tangentSpacePoly, Submodule.mem_iInf]

end MvPolynomial
end
