import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Basic

set_option autoImplicit false

noncomputable section

/-! # Translated tangent spaces (ATLAS ArithmeticGeometry Definition 17.1)

This module formalizes translated tangent vectors at a point `P`:
the total derivative of a polynomial along a direction `v`,
its linearization, and the tangent spaces of a hypersurface and of an ideal.
-/

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
