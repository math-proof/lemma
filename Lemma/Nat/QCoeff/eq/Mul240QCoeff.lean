import Mathlib
import sympy.Basic
import Def.FLTPrelim_Modularity
open scoped MatrixGroups


private lemma ModularForm.levelOne_weight_four_qCoeff_one (Y : ModularForm 𝒮ℒ 4) : ModularFormClass.qCoeff ⇑Y 1 = 240 * ModularFormClass.qCoeff ⇑Y 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ModularForm.E₄ = Y :=
    (finrank_eq_one_iff_of_nonzero' ModularForm.E₄ (EisensteinSeries.E_ne_zero _ ⟨2, rfl⟩)).mp
      (Module.rank_eq_one_iff_finrank_eq_one.mp ModularForm.levelOne_weight_four_rank_one) Y
  have hq : UpperHalfPlane.qExpansion 1 ⇑Y = c • UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄ := by
    rw [← ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c ModularForm.E₄,
      show (c • ⇑ModularForm.E₄) = ⇑Y from congrArg DFunLike.coe hc]
  have h0 : (UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₄).coeff 0 = 1 :=
    EisensteinSeries.E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  show (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 1 = _ * (UpperHalfPlane.qExpansion 1 ⇑Y).coeff 0
  rw [hq, PowerSeries.coeff_smul, PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul, h0,
    ModularForm.E₄_qExpansion_coeff_one]
  ring
/--
[ModularForm_levelOne_weight_four_qCoeff_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_levelOne_weight_four_qCoeff_one.lean)
-/
@[path]
private lemma main
  {Y : ModularForm 𝒮ℒ 4} :
-- imply
  ModularFormClass.qCoeff ⇑Y 1 = 240 * ModularFormClass.qCoeff ⇑Y 0 :=
-- proof
  ModularForm.levelOne_weight_four_qCoeff_one Y


-- created on 2026-10-23
