import Mathlib
import Lemma.ModularCurve.CharLFrobeniusGeomLevel

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section AbstractDictionary

variable {J' : Type*} [AddCommGroup J'] [Module HeckeAlg J']
variable {ℓ : ℕ}

private theorem specialFibreRelation_of_decomp_of_verFrob_aux (hℓ : ℓ.Prime)
    {F V T : J' →+ J'}
    (hdecomp : ∀ y : J', T y = F y + V y)
    (hVF : ∀ y : J', V (F y) = ℓ • y)
    (hmatch : ∀ y : J', heckeGen ⟨ℓ, hℓ⟩ • y = T y) :
    SpecialFibreRelation J' ℓ hℓ F := by
  intro y
  rw [hmatch, hdecomp, hVF]; abel

end AbstractDictionary

section Bridge

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (hperf : ∀ c : K, ∃ d : K, d ^ ℓ = c)
variable (hdeg1 : ∀ w : Place K (modularFunctionFieldC K N), w.deg = 1)

theorem specialFibreRelation_pic0_level_of_match
    (inst : Module HeckeAlg (Pic0 K (modularFunctionFieldC K N)))
    (hmatch : ∀ x, (letI := inst; heckeGen ⟨ℓ, hℓ.out⟩ • x)
        = heckeFibreGeomLevelPic0 K N data hKr hperf hdeg1 x) :
    letI := inst
    SpecialFibreRelation (Pic0 K (modularFunctionFieldC K N)) ℓ hℓ.out
      (frobeniusPushforwardGeomLevelPic0 K N data hKr hperf hdeg1) := by
  letI := inst
  refine specialFibreRelation_of_decomp_of_verFrob_aux hℓ.out
    (V := frobeniusPullbackGeomLevelPic0 K N data hKr hperf hdeg1)
    (T := heckeFibreGeomLevelPic0 K N data hKr hperf hdeg1)
    (heckeFibreGeomLevelPic0_eq_add K N data hKr hperf hdeg1)
    (fun y => ?_) hmatch
  have h := frobeniusPullbackGeomLevelPic0_frobeniusPushforwardGeomLevelPic0
    K N data hKr hperf hdeg1 y
  rw [h, natCast_zsmul]

variable [IsAlgClosed K] [IsCurveOver K (modularFunctionFieldC K N)]

theorem specialFibreRelation_pic0_level_of_isCurveOver_of_match
    (inst : Module HeckeAlg (Pic0 K (modularFunctionFieldC K N)))
    (hmatch : SpecialFibreHeckeModuleMatch K N data hKr inst) :
    letI := inst
    SpecialFibreRelation (Pic0 K (modularFunctionFieldC K N)) ℓ hℓ.out
      (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr) :=
  specialFibreRelation_pic0_level_of_match K N data hKr (perfect_of_isAlgClosed K)
    (deg_eq_one_modularFunctionFieldC K N) inst hmatch

end Bridge

section ForallM

variable (K : Type*) [Field K] [IsAlgClosed K]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
variable (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
variable (hfam : IsCurveOverModularFunctionFieldCFamily K)

theorem forall_eichlerShimura_special_fibre_pic0_of_curveOverFamily :
    ∀ (N : ℕ) [NeZero N],
      letI := hfam N
      ∀ x : Pic0 K (modularFunctionFieldC K N),
        frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr
            (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr x)
          - heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr
              (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr x)
          + (ℓ : ℤ) • x = 0 := by
  intro N _
  letI := hfam N
  exact eichlerShimura_special_fibre_pic0_level_of_isCurveOver K N data hKr

theorem forall_heckeFibreGeomLevelPic0_eq_add_of_curveOverFamily :
    ∀ (N : ℕ) [NeZero N],
      letI := hfam N
      ∀ x : Pic0 K (modularFunctionFieldC K N),
        heckeFibreGeomLevelPic0OfIsCurveOver K N data hKr x
          = frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr x
            + frobeniusPullbackGeomLevelPic0OfIsCurveOver K N data hKr x := by
  intro N _
  letI := hfam N
  exact heckeFibreGeomLevelPic0OfIsCurveOver_eq_add K N data hKr

theorem forall_frobeniusPullbackPushforwardGeomLevelPic0_of_curveOverFamily :
    ∀ (N : ℕ) [NeZero N],
      letI := hfam N
      ∀ x : Pic0 K (modularFunctionFieldC K N),
        frobeniusPullbackGeomLevelPic0OfIsCurveOver K N data hKr
            (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr x)
          = (ℓ : ℤ) • x := by
  intro N _
  letI := hfam N
  exact frobeniusPullbackPushforwardGeomLevelPic0OfIsCurveOver K N data hKr

theorem forall_specialFibreRelation_pic0_of_curveOverFamily_of_matchFamily
    (instfam : ∀ (N : ℕ) [NeZero N],
      letI := hfam N; Module HeckeAlg (Pic0 K (modularFunctionFieldC K N)))
    (hmatchfam : ∀ (N : ℕ) [NeZero N],
      letI := hfam N; SpecialFibreHeckeModuleMatch K N data hKr (instfam N)) :
    ∀ (N : ℕ) [NeZero N],
      letI := hfam N; letI := instfam N
      SpecialFibreRelation (Pic0 K (modularFunctionFieldC K N)) ℓ (Fact.out)
        (frobeniusPushforwardGeomLevelPic0OfIsCurveOver K N data hKr) := by
  intro N _
  letI := hfam N
  exact specialFibreRelation_pic0_level_of_isCurveOver_of_match K N data hKr
    (instfam N) (hmatchfam N)

end ForallM

end ModularCurve
