import Mathlib
import sympy.Basic
import Def.FLTPrelim_Modularity
import Lemma.Int.P2MUtil
open scoped MatrixGroups


private lemma exists_coe_eq_smul_discriminant (Z : ModularForm 𝒮ℒ 12) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : ∃ c : ℂ, (⇑Z : UpperHalfPlane → ℂ) = c • ⇑CuspForm.discriminant := by
  obtain ⟨c, hc⟩ :=
    CuspForm.exists_smul_discriminant_of_weight_eq_twelve (ModularForm.toCuspForm Z h0)
  exact ⟨c, (show (c • ⇑CuspForm.discriminant : UpperHalfPlane → ℂ) = ⇑(ModularForm.toCuspForm Z h0) from congrArg DFunLike.coe hc).symm⟩

private lemma qExpansion_eq_smul (Z : ModularForm 𝒮ℒ 12) (c : ℂ) (hZ : (⇑Z : UpperHalfPlane → ℂ) = c • ⇑CuspForm.discriminant) : UpperHalfPlane.qExpansion 1 ⇑Z = c • UpperHalfPlane.qExpansion 1 ModularForm.discriminant := by
  rw [hZ, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c CuspForm.discriminant,
    CuspForm.coe_discriminant]

private lemma qCoeff_eq_mul (Z : ModularForm 𝒮ℒ 12) (c : ℂ) (hq : UpperHalfPlane.qExpansion 1 ⇑Z = c • UpperHalfPlane.qExpansion 1 ModularForm.discriminant) (n : ℕ) : ModularFormClass.qCoeff ⇑Z n = c * ModularFormClass.qCoeff ModularForm.discriminant n := by
  unfold ModularFormClass.qCoeff
  rw [hq, PowerSeries.coeff_smul, smul_eq_mul]

private lemma qCoeff_one_eq (Z : ModularForm 𝒮ℒ 12) (c : ℂ) (hq : UpperHalfPlane.qExpansion 1 ⇑Z = c • UpperHalfPlane.qExpansion 1 ModularForm.discriminant) : ModularFormClass.qCoeff ⇑Z 1 = c := by
  have h1 : ModularFormClass.qCoeff ModularForm.discriminant 1 = 1 := by
    unfold ModularFormClass.qCoeff
    exact ModularForm.discriminant_qExpansion_coeff_one
  rw [qCoeff_eq_mul Z c hq 1, h1, mul_one]

p2m_open_scoped "ModularForm" in

private lemma ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant (Z : ModularForm 𝒮ℒ 12) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n = ModularFormClass.qCoeff ⇑Z 1 * ModularFormClass.qCoeff ModularForm.discriminant n := by
  obtain ⟨c, hZ⟩ := exists_coe_eq_smul_discriminant Z h0
  have hq := qExpansion_eq_smul Z c hZ
  intro n
  rw [qCoeff_eq_mul Z c hq n, qCoeff_one_eq Z c hq]
/--
[ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant.lean)
-/
@[path]
private lemma main
  {Z : ModularForm 𝒮ℒ 12}
-- given
  (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) :
-- imply
  ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n = ModularFormClass.qCoeff ⇑Z 1 * ModularFormClass.qCoeff ModularForm.discriminant n :=
-- proof
  ModularForm.levelOne_weight_twelve_qCoeff_eq_qCoeff_one_mul_discriminant Z h0


-- created on 2026-10-23
