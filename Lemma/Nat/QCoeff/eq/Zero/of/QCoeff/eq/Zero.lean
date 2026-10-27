import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.FLTPrelim_Modularity
import Lemma.Int.P2MUtil
open scoped MatrixGroups


private lemma rank_cuspForm_fourteen_eq_zero : Module.rank ℂ (CuspForm 𝒮ℒ 14) = 0 :=
  CuspForm.discriminantEquiv.rank_eq.trans ModularForm.levelOne_weight_two_rank_zero

private lemma toCuspForm_eq_zero (Z : ModularForm 𝒮ℒ 14) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : Eq (ModularForm.toCuspForm Z h0) 0 :=
  rank_zero_iff_forall_zero.mp rank_cuspForm_fourteen_eq_zero _

private lemma coe_eq_zero (Z : ModularForm 𝒮ℒ 14) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) :
  (⇑Z : UpperHalfPlane → ℂ) = 0 := by
  show (⇑(ModularForm.toCuspForm Z h0) : UpperHalfPlane → ℂ) = 0
  rw [toCuspForm_eq_zero Z h0, CuspForm.coe_zero]

p2m_open_scoped "ModularForm" in

private lemma ModularForm.levelOne_weight_fourteen_qCoeff_eq_zero (Z : ModularForm 𝒮ℒ 14) (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) : ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n = 0 := by
  intro n
  unfold ModularFormClass.qCoeff
  rw [coe_eq_zero Z h0, UpperHalfPlane.qExpansion_zero, map_zero]
/--
[ModularForm_levelOne_weight_fourteen_qCoeff_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularForm_levelOne_weight_fourteen_qCoeff_eq_zero.lean)
-/
@[path]
private lemma main
  {Z : ModularForm 𝒮ℒ 14}
-- given
  (h0 : ModularFormClass.qCoeff ⇑Z 0 = 0) :
-- imply
  ∀ n : ℕ, ModularFormClass.qCoeff ⇑Z n = 0 :=
-- proof
  ModularForm.levelOne_weight_fourteen_qCoeff_eq_zero Z h0


-- created on 2026-10-23
