import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Structure.GaloisRep_Adic

namespace GaloisRep

structure DeformationRingData (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop) :
    Type 1 where

  R : Type
  [instCommRing : CommRing R]
  [instIsLocalRing : IsLocalRing R]
  [instIsNoetherianRing : IsNoetherianRing R]
  [instIsAdicComplete : IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  [instAlgebra : Algebra 𝒪 R]
  [instIsLocalHom : IsLocalHom (algebraMap 𝒪 R)]

  residue_surjective : Function.Surjective (IsLocalRing.residue R ∘ algebraMap 𝒪 R)

  absIrr : ρbar.IsAbsolutelyIrreducible

  ρ : GaloisRepAdic R

  isOfType : 𝒟 ρ

  residual_isEquiv : ρ.residual.IsEquiv
    (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 R)))

  universal : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)],
      Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A) →
      ∀ ρA : GaloisRepAdic A, 𝒟 ρA →
        ρA.residual.IsEquiv
          (ρbar.baseChangeAlong (IsLocalRing.ResidueField.map (algebraMap 𝒪 A))) →
        ∃! φ : R →ₐ[𝒪] A, ∃ hφ : IsLocalHom (φ : R →+* A),
          (ρ.baseChangeAlong (φ : R →+* A) hφ).IsEquiv ρA

attribute [instance] DeformationRingData.instCommRing DeformationRingData.instIsLocalRing
  DeformationRingData.instIsNoetherianRing DeformationRingData.instIsAdicComplete
  DeformationRingData.instAlgebra DeformationRingData.instIsLocalHom

end GaloisRep
