import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Basic
set_option autoImplicit false

/-! # Translated tangent spaces (ATLAS ArithmeticGeometry Definition 17.1)

This module formalizes translated tangent vectors at a point `P`:
the total derivative of a polynomial along a direction `v`,
its linearization, and the tangent spaces of a hypersurface and of an ideal.
-/


noncomputable section

namespace MvPolynomial

variable {k : Type*} [Field k] {n : Nat}

/-- Total derivative of `f` at `P` along the translated direction `v`.

This is the directional derivative `∑ i, ∂ᵢ f (P) * v i`,
preserving the audited ATLAS construction verbatim. -/
def totalDerivativeAt (f : MvPolynomial (Fin n) k) (P v : Fin n → k) : k :=
  ∑ i : Fin n, MvPolynomial.eval P (MvPolynomial.pderiv i f) * v i

/-- Linearization of `totalDerivativeAt f P` in the direction `v`. -/
def totalDerivativeAtLin (f : MvPolynomial (Fin n) k) (P : Fin n → k) :
    (Fin n → k) →ₗ[k] k where
  toFun := totalDerivativeAt f P
  map_add' x y := by
    simp only [totalDerivativeAt, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [totalDerivativeAt, Pi.smul_apply, smul_eq_mul, mul_left_comm,
      ← Finset.mul_sum, RingHom.id_apply]

/-- Tangent space of the hypersurface cut out by `f` at `P`,
as the kernel of the total derivative. -/
def tangentSpacePoly (f : MvPolynomial (Fin n) k) (P : Fin n → k) :
    Submodule k (Fin n → k) :=
  LinearMap.ker (totalDerivativeAtLin f P)

/-- Tangent space of the ideal `I` at `P`,
as the simultaneous kernel for all `f ∈ I`. -/
def tangentSpaceIdeal (I : Ideal (MvPolynomial (Fin n) k)) (P : Fin n → k) :
    Submodule k (Fin n → k) :=
  ⨅ f ∈ I, tangentSpacePoly f P

end MvPolynomial
end
