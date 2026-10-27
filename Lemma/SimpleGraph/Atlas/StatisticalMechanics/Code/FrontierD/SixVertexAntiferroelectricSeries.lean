import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexAntiferroelectricLambda_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricLambda_pos_eq
  {c : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexAntiferroelectricLambda c := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricLambda_pos hc

/--
[sixVertex_cosh_antiferroelectricLambda](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma sixVertex_cosh_antiferroelectricLambda_eq
  {c : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  Real.cosh (sixVertexAntiferroelectricLambda c) = (c ^ 2 - 2) / 2 := by
-- proof
  apply StatMech.FrontierD.sixVertex_cosh_antiferroelectricLambda hc

/--
[sixVertexAntiferroelectricLambda_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricLambda_unique_eq
  {c lam : ℝ}
-- given
  (hlam : 0 < lam)
  (hcosh : Real.cosh lam = (c ^ 2 - 2) / 2) :
-- imply
  lam = sixVertexAntiferroelectricLambda c := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricLambda_unique hlam hcosh

/--
[sixVertexFreeEnergySeriesTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma sixVertexFreeEnergySeriesTerm_nonneg_eq
  {lam : ℝ}
  {n : ℕ}
-- given
  (hlam : 0 < lam) :
-- imply
  0 ≤ sixVertexFreeEnergySeriesTerm lam n := by
-- proof
  apply StatMech.FrontierD.sixVertexFreeEnergySeriesTerm_nonneg hlam n

/--
[sixVertexFreeEnergySeriesTerm_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma sixVertexFreeEnergySeriesTerm_norm_le_eq
  {lam : ℝ}
  {n : ℕ}
-- given
  (hlam : 0 < lam) :
-- imply
  ‖sixVertexFreeEnergySeriesTerm lam n‖ ≤ Real.exp (-lam) ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFreeEnergySeriesTerm_norm_le hlam n

/--
[summable_sixVertexFreeEnergySeriesTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma summable_sixVertexFreeEnergySeriesTerm_eq
  {lam : ℝ}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (sixVertexFreeEnergySeriesTerm lam) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexFreeEnergySeriesTerm hlam

/--
[one_sub_tanh_le_two_mul_exp_neg_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma one_sub_tanh_le_two_mul_exp_neg_two_mul_eq
  {x : ℝ} :
-- imply
  1 - Real.tanh x ≤ 2 * Real.exp (-2 * x) := by
-- proof
  apply StatMech.FrontierD.one_sub_tanh_le_two_mul_exp_neg_two_mul x

/--
[tanh_sub_one_eq_neg_two_mul_exp_neg_two_mul_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma tanh_sub_one_eq_neg_two_mul_exp_neg_two_mul_div_eq
  {x : ℝ} :
-- imply
  Real.tanh x - 1 = -2 * Real.exp (-2 * x) / (1 + Real.exp (-2 * x)) := by
-- proof
  apply StatMech.FrontierD.tanh_sub_one_eq_neg_two_mul_exp_neg_two_mul_div x

/--
[sixVertexGapCorrectionTerm_eq_lambert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma sixVertexGapCorrectionTerm_eq_lambert_eq
  {lam : ℝ}
  {n : ℕ} :
-- imply
  sixVertexGapCorrectionTerm lam n = sixVertexGapLambertTerm lam n := by
-- proof
  apply StatMech.FrontierD.sixVertexGapCorrectionTerm_eq_lambert lam n

/--
[sixVertexGapCorrectionTerm_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma sixVertexGapCorrectionTerm_norm_le_eq
  {lam : ℝ}
  {n : ℕ} :
-- imply
  ‖sixVertexGapCorrectionTerm lam n‖ ≤ 2 * Real.exp (-2 * lam) ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexGapCorrectionTerm_norm_le lam n

/--
[summable_sixVertexGapCorrectionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma summable_sixVertexGapCorrectionTerm_eq
  {lam : ℝ}
-- given
  (hlam : 0 < lam) :
-- imply
  Summable (sixVertexGapCorrectionTerm lam) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexGapCorrectionTerm hlam

/--
[sixVertexAlternatingHarmonicLimit_eq_log_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma sixVertexAlternatingHarmonicLimit_eq_log_two_eq :
-- imply
  sixVertexAlternatingHarmonicLimit = Real.log 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexAlternatingHarmonicLimit_eq_log_two

/--
[sixVertexGapSeries_eq_lambert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma sixVertexGapSeries_eq_lambert_eq
  {lam : ℝ} :
-- imply
  sixVertexGapSeries lam = -Real.log 2 + ∑' n : ℕ, sixVertexGapLambertTerm lam n := by
-- proof
  apply StatMech.FrontierD.sixVertexGapSeries_eq_lambert lam

/--
[sixVertexGapSeries_partialSum_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAntiferroelectricSeries.lean)
-/
@[path]
private lemma sixVertexGapSeries_partialSum_tendsto_eq
  {lam : ℝ}
-- given
  (hlam : 0 < lam) :
-- imply
  Tendsto (fun N : ℕ => ∑ n ∈ range N, sixVertexGapSeriesTerm lam n) atTop (𝓝 (sixVertexGapSeries lam)) := by
-- proof
  apply StatMech.FrontierD.sixVertexGapSeries_partialSum_tendsto hlam


-- created on 2026-10-23
