import Lemma.Definitions.Def_ModularCurve_CharLSpecialFibrePic0ForallMBridge
import Lemma.Definitions.Def_ModularCurve_SpecializationWitness

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1200000

noncomputable section
open AlgebraicCurve

namespace ModularCurve

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable [IsAlgClosed K] [IsCurveOver K (modularFunctionFieldC K N)]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

def Pic0SpecialFibreCommutingFamilyMatch
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N))) : Prop :=
  fam.T ⟨ℓ, hℓ.out⟩
    = (heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr).toIntLinearMap

theorem pic0SpecialFibreCommutingFamilyMatch_iff
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N))) :
    Pic0SpecialFibreCommutingFamilyMatch K N data hKr fam
      ↔ ∀ x, fam.T ⟨ℓ, hℓ.out⟩ x
          = heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr x := by
  refine ⟨fun h x => h ▸ rfl, fun h => ?_⟩
  ext x; exact h x

theorem specialFibreHeckeModuleMatch_of_commutingFamily
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N)))
    (hfam : Pic0SpecialFibreCommutingFamilyMatch K N data hKr fam) :
    SpecialFibreHeckeModuleMatch K N data hKr fam.module := by
  intro x
  rw [fam.module_heckeGen_smul ⟨ℓ, hℓ.out⟩ x, hfam]
  rfl

theorem specialFibreRelation_pic0_level_of_commutingFamily
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N)))
    (hfam : Pic0SpecialFibreCommutingFamilyMatch K N data hKr fam) :
    letI := fam.module
    SpecialFibreRelation (Pic0 K (modularFunctionFieldC K N)) ℓ hℓ.out
      (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr) :=
  specialFibreRelation_pic0_level_of_isCurveOver_of_match K N data hKr fam.module
    (specialFibreHeckeModuleMatch_of_commutingFamily K N data hKr fam hfam)

theorem specializationWitnessData_relation_of_commutingFamily
    (fam : CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K N)))
    (hfam : Pic0SpecialFibreCommutingFamilyMatch K N data hKr fam)
    (y : Pic0 K (modularFunctionFieldC K N)) :
    frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr
        (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr y)
      - fam.T ⟨ℓ, hℓ.out⟩ (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr y)
      + ℓ • y = 0 := by
  rw [(pic0SpecialFibreCommutingFamilyMatch_iff K N data hKr fam).mp hfam,
    ← natCast_zsmul]
  exact eichlerShimura_special_fibre_pic0_level_of_isCurveOver K N data hKr y

variable (hcofam : IsCurveOverModularFunctionFieldCFamily K)

theorem forall_specialFibreRelation_pic0_of_commutingFamily_family
    (famfam : ∀ (M : ℕ) [NeZero M],
      letI := hcofam M
      CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K M)))
    (hfamfam : ∀ (M : ℕ) [NeZero M],
      letI := hcofam M
      Pic0SpecialFibreCommutingFamilyMatch K M data hKr (famfam M)) :
    ∀ (M : ℕ) [NeZero M],
      letI := hcofam M; letI := (famfam M).module
      SpecialFibreRelation (Pic0 K (modularFunctionFieldC K M)) ℓ (Fact.out)
        (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K M data hKr) := by
  intro M _
  letI := hcofam M
  exact specialFibreRelation_pic0_level_of_commutingFamily K M data hKr
    (famfam M) (hfamfam M)

theorem forall_specializationWitnessData_relation_of_commutingFamily_family
    (famfam : ∀ (M : ℕ) [NeZero M],
      letI := hcofam M
      CommutingHeckeFamily (Pic0 K (modularFunctionFieldC K M)))
    (hfamfam : ∀ (M : ℕ) [NeZero M],
      letI := hcofam M
      Pic0SpecialFibreCommutingFamilyMatch K M data hKr (famfam M)) :
    ∀ (M : ℕ) [NeZero M],
      letI := hcofam M
      ∀ y : Pic0 K (modularFunctionFieldC K M),
        frobeniusPushforwardGeomLevelPic0OfIsCurveOver K M data hKr
            (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K M data hKr y)
          - (famfam M).T ⟨ℓ, hℓ.out⟩
              (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K M data hKr y)
          + ℓ • y = 0 := by
  intro M _
  letI := hcofam M
  exact specializationWitnessData_relation_of_commutingFamily K M data hKr
    (famfam M) (hfamfam M)

end ModularCurve
