import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_FLTPrelim_Modularity
open scoped MatrixGroups


private lemma ModularForm.levelOne_weight_six_qCoeff_one (Y : ModularForm 𝒮ℒ 6) : ModularFormClass.qCoeff ⇑Y 1 = -504 * ModularFormClass.qCoeff ⇑Y 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ModularForm.E₆ = Y :=
    (finrank_eq_one_iff_of_nonzero' ModularForm.E₆ (EisensteinSeries.E_ne_zero _ ⟨3, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_six_rank_one) Y
  have hq : UpperHalfPlane.qExpansion 1 ⇑Y = c • UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ := by
    rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c ModularForm.E₆,
      show (c • ⇑ModularForm.E₆) = ⇑Y from congrArg DFunLike.coe hc]
  have h0 : (UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨3, rfl⟩
  show (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 1 = _ * (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 0
  rw [hq, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul, h0,
    ModularForm.E₆_qExpansion_coeff_one]
  ring
/--
[ModularForm_levelOne_weight_six_qCoeff_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_levelOne_weight_six_qCoeff_one.lean)
-/
@[path]
private lemma main
  {Y : ModularForm 𝒮ℒ 6} :
-- imply
  ModularFormClass.qCoeff ⇑Y 1 = -504 * ModularFormClass.qCoeff ⇑Y 0 :=
-- proof
  ModularForm.levelOne_weight_six_qCoeff_one Y


-- created on 2026-10-23
