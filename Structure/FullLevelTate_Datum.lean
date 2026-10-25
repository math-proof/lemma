import Structure.GaloisRep_Adic
import Instance.CuspidalType_IsCuspidalOfType
import Structure.HeckeGalois_EichlerShimura

set_option autoImplicit false

noncomputable section

namespace FullLevelTate

structure Datum (q : ℕ) [Fact q.Prime] (M' : ℕ) (O' : Type) [CommRing O'] [IsLocalRing O'] :
    Type 1 where

  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module O' V]
  [instFree : Module.Free O' V]
  [instFinite : Module.Finite O' V]

  gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End O' V

  gal_isAdicContinuous : GaloisActionIsAdicContinuous O' gal

  gl2 : CuspidalType.GL2 q →* Module.End O' V

  hecke : ModularCurve.HeckeAlg →+* Module.End O' V

  gal_comm_gl2 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : CuspidalType.GL2 q),
    gal σ * gl2 x = gl2 x * gal σ

  hecke_comm_gal : ∀ (t : ModularCurve.HeckeAlg) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
    hecke t * gal σ = gal σ * hecke t

  hecke_comm_gl2 : ∀ (t : ModularCurve.HeckeAlg) (x : CuspidalType.GL2 q),
    hecke t * gl2 x = gl2 x * hecke t

  unramified : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → ¬ ℓ ∣ M' → (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, gal σ = 1

  eichlerShimura : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ.Coprime q), ¬ ℓ ∣ M' →
    (ℓ : O') ∉ IsLocalRing.maximalIdeal O' →
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
        gal σ * gal σ - hecke (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) * gal σ
          + (ℓ : O') • gl2 (CuspidalType.scalarElem q (ZMod.unitOfCoprime ℓ hℓq)) = 0

attribute [instance] Datum.instAddCommGroup Datum.instModule Datum.instFree Datum.instFinite

example (q : ℕ) [Fact q.Prime] (M' : ℕ) (O' : Type) [CommRing O'] [IsLocalRing O'] :
    Datum q M' O' where
  V := Fin 0 → O'
  gal := 1
  gal_isAdicContinuous := fun n =>
    ⟨⊥, inferInstance, fun σ _ v => by rw [MonoidHom.one_apply, Module.End.one_apply, sub_self]; exact zero_mem _⟩
  gl2 := 1
  hecke := (algebraMap O' (Module.End O' (Fin 0 → O'))).comp
    (MvPolynomial.eval₂Hom (Int.castRingHom O') 0)
  gal_comm_gl2 := fun σ x => by rw [MonoidHom.one_apply, MonoidHom.one_apply]
  hecke_comm_gal := fun t σ => by rw [MonoidHom.one_apply, mul_one, one_mul]
  hecke_comm_gl2 := fun t x => by rw [MonoidHom.one_apply, mul_one, one_mul]
  unramified := fun _ _ _ _ _ _ _ _ _ => MonoidHom.one_apply _
  eichlerShimura := fun _ _ _ _ _ _ _ _ _ => LinearMap.ext fun v => Subsingleton.elim _ _

end FullLevelTate

end
