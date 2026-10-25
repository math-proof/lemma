import Def.CerednikDrinfeld_QMCanonicalPol

set_option autoImplicit false

noncomputable section

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation CerednikDrinfeld.QM

namespace AlgebraicGeometry.PolarisedAbelianScheme

variable {a b : ℚ}

structure QMStructure (Λ : Submodule ℤ ℍ[ℚ, a, b]) (star : ↥Λ → ↥Λ) (β : Fin (2 * 2) → ↥Λ)
    {d m : ℕ} {S : Type} [CommRing S] (X : PolarisedAbelianScheme 2 d m S) : Type 1 where

  act : ↥Λ → (X.A ⟶ X.A)

  act_over : ∀ x : ↥Λ, act x ≫ X.f = X.f

  act_hom : ∀ (x : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t X.f),
    pushPt (act x) (act_over x) (X.L.mul t P Q) = X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q)

  act_one : ∀ h : (1 : ℍ[ℚ, a, b]) ∈ Λ, act ⟨1, h⟩ = 𝟙 X.A

  act_mul : ∀ (x y : ↥Λ) (h : (x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]) ∈ Λ),
    act ⟨(x : ℍ[ℚ, a, b]) * (y : ℍ[ℚ, a, b]), h⟩ = act y ≫ act x

  act_add : ∀ (x y : ↥Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t X.f),
    pushPt (act (x + y)) (act_over (x + y)) P =
      X.L.mul t (pushPt (act x) (act_over x) P) (pushPt (act y) (act_over y) P)

  act_trace : ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k)
    (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) X.f),
    Function.Injective τ →
    (∀ P : SchemeHomOver (tangentBase k sk) X.f, P ∈ Set.range τ ↔ IsTangentVector X.L k sk P) →
    (∀ v w : V, τ (v + w) = X.L.mul (tangentBase k sk) (τ v) (τ w)) →
    (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
    ∀ (x : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act x) (act_over x) (τ v)) →
    ∀ n : ℤ, (x : ℍ[ℚ, a, b]) + Star.star (x : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
      LinearMap.trace k V Φ = (n : k)

  P : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) X.f

  level_match : ∀ j : Fin (2 * 2), pushPt (act (β j)) (act_over (β j)) P = X.P j

  pol_canonical : ∃ polE : X.A.Modules, CerednikDrinfeld.QM.IsCanonicalPolData X.f X.L act act_over star polE ∧
    LocIsoOnBase X.f X.pol (polE ⊗ polE ⊗ polE)

namespace QMStructure

variable {Λ : Submodule ℤ ℍ[ℚ, a, b]} {star : ↥Λ → ↥Λ} {β : Fin (2 * 2) → ↥Λ} {d m : ℕ}


end QMStructure

end AlgebraicGeometry.PolarisedAbelianScheme

end
