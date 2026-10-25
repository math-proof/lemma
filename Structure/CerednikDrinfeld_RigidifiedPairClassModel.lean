import Structure.CerednikDrinfeld_QMRigidification
import Structure.CerednikDrinfeld_QMFineModuli
import Structure.CerednikDrinfeld_QMFineModuliT
import Structure.CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

namespace CerednikDrinfeld.QM.RigidifiedPairClass

structure Pt {C : Type} [CommRing C] (πC : C) {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C))
    (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC) (T : Type) [CommRing T] [Algebra C T] where

  t : Spec (CommRingCat.of T) ⟶ MC
  ht : t ≫ g = Spec.map (CommRingCat.ofHom (algebraMap C T))

  d : ℕ

  x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T πC})) ⟶ X d
  hx : x ≫ ξ d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T πC}))) ≫ t


section Model

variable {r N : ℕ} (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr]
  {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
  (A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})) (n : ℕ)
  (C : Type) [CommRing C] [Algebra 𝒪 C] (ψ : Onr →ₐ[𝒪] C)
  {MC : Scheme.{0}} (g : MC ⟶ Spec (CommRingCat.of C)) (X : ℕ → Scheme.{0}) (ξ : ∀ d, X d ⟶ MC)

  (tM : ∀ (T : Type) [CommRing T] [Algebra C T],
    FakeEllipticCurve.WithFullLevel Λ N n T → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap C T))) g)

  (xOf : ∀ (T : Type) [CommRing T] [Algebra C T] [Algebra 𝒪 T] [IsScalarTower 𝒪 C T]
    (ψT : Onr →ₐ[𝒪] T) (_ : ψT = (IsScalarTower.toAlgHom 𝒪 C T).comp ψ)
    (u : FakeEllipticCurve.WithFullLevel Λ N n T) (ρ : FakeEllipticCurve.Rigidification r π A₀ ψT u.1),
    { x : Spec (CommRingCat.of (T ⧸ Ideal.span {algebraMap C T (algebraMap 𝒪 C π)})) ⟶ X ρ.d //
      x ≫ ξ ρ.d = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {algebraMap C T (algebraMap 𝒪 C π)}))) ≫ (tM T u).1 })


end Model

end CerednikDrinfeld.QM.RigidifiedPairClass
