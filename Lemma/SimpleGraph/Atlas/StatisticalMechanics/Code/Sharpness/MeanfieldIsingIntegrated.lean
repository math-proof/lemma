import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingIntegrated.Part5
open MeasureTheory Real Set Filter Topology StatMech StatMech.Sharpness


/--
[hasDerivAt_sctOriginMag_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma hasDerivAt_sctOriginMag_beta_eq
  {d n : ℕ}
-- given
  (h beta : ℝ) :
-- imply
  HasDerivAt (fun b => sctOriginMag d b h n) (sctOriginMagBetaDeriv d n h beta) beta := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_sctOriginMag_beta d n h beta

/--
[hasDerivAt_sctOriginMag_sq_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma hasDerivAt_sctOriginMag_sq_beta_eq
  {d n : ℕ}
-- given
  (h beta : ℝ) :
-- imply
  HasDerivAt (fun b => (sctOriginMag d b h n) ^ 2) (sctOriginMagSqBetaDeriv d n h beta) beta := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_sctOriginMag_sq_beta d n h beta

/--
[deriv_sctOriginMag_sq_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma deriv_sctOriginMag_sq_beta_eq
  {d n : ℕ}
-- given
  (h beta : ℝ) :
-- imply
  deriv (fun b => (sctOriginMag d b h n) ^ 2) beta = sctOriginMagSqBetaDeriv d n h beta := by
-- proof
  apply StatMech.Sharpness.deriv_sctOriginMag_sq_beta d n h beta

/--
[hasDerivAt_sctMeanfieldG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma hasDerivAt_sctMeanfieldG_eq
  {d n : ℕ}
-- given
  (h beta : ℝ) :
-- imply
  HasDerivAt (sctMeanfieldG d n h) (sctMeanfieldGDeriv d n h beta) beta := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_sctMeanfieldG d n h beta

/--
[continuous_isingExpectation_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma continuous_isingExpectation_beta_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (h : ℝ) :
-- imply
  Continuous (fun beta => isingExpectation G beta h f) := by
-- proof
  apply StatMech.Sharpness.continuous_isingExpectation_beta G h f

/--
[continuous_sctBoxMag_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma continuous_sctBoxMag_beta_eq
  {d n : ℕ}
  {x : sctBox d n}
-- given
  (h : ℝ) :
-- imply
  Continuous (fun beta => sctBoxMag d beta h n x) := by
-- proof
  apply StatMech.Sharpness.continuous_sctBoxMag_beta d n h x

/--
[continuous_sctOriginMag_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma continuous_sctOriginMag_beta_eq
  {d n : ℕ}
-- given
  (h : ℝ) :
-- imply
  Continuous (fun beta => sctOriginMag d beta h n) := by
-- proof
  apply StatMech.Sharpness.continuous_sctOriginMag_beta d n h

/--
[continuous_sctOriginMagBetaDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma continuous_sctOriginMagBetaDeriv_eq
  {d n : ℕ}
-- given
  (h : ℝ) :
-- imply
  Continuous (sctOriginMagBetaDeriv d n h) := by
-- proof
  apply StatMech.Sharpness.continuous_sctOriginMagBetaDeriv d n h

/--
[continuous_sctOriginMagSqBetaDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma continuous_sctOriginMagSqBetaDeriv_eq
  {d n : ℕ}
-- given
  (h : ℝ) :
-- imply
  Continuous (sctOriginMagSqBetaDeriv d n h) := by
-- proof
  apply StatMech.Sharpness.continuous_sctOriginMagSqBetaDeriv d n h

/--
[continuous_sctMeanfieldGDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma continuous_sctMeanfieldGDeriv_eq
  {d n : ℕ}
-- given
  (h : ℝ) :
-- imply
  Continuous (sctMeanfieldGDeriv d n h) := by
-- proof
  apply StatMech.Sharpness.continuous_sctMeanfieldGDeriv d n h

/--
[continuousOn_sctLatticeC_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma continuousOn_sctLatticeC_beta_eq
  {d n : ℕ}
  {a b : ℝ}
-- given
  (h : ℝ)
  (hh : 0 < h)
  (ha : 0 < a) :
-- imply
  ContinuousOn (fun beta => sctLatticeC d beta h n) (Icc a b) := by
-- proof
  apply StatMech.Sharpness.continuousOn_sctLatticeC_beta d n h hh ha

/--
[continuous_sctBoxCovariance_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma continuous_sctBoxCovariance_beta_eq
  {d n : ℕ}
  {x : sctBox d n}
-- given
  (h : ℝ) :
-- imply
  Continuous (fun beta => sctBoxCovariance d beta h n x) := by
-- proof
  apply StatMech.Sharpness.continuous_sctBoxCovariance_beta d n h x

/--
[continuous_sctBoundaryCovarianceError_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma continuous_sctBoundaryCovarianceError_beta_eq
  {d n : ℕ}
-- given
  (h : ℝ) :
-- imply
  Continuous (fun beta => sctBoundaryCovarianceError d beta h n) := by
-- proof
  apply StatMech.Sharpness.continuous_sctBoundaryCovarianceError_beta d n h

/--
[continuousOn_sctMeanfieldIntegratedError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma continuousOn_sctMeanfieldIntegratedError_eq
  {d n : ℕ}
  {a b : ℝ}
-- given
  (h : ℝ)
  (hh : 0 < h)
  (ha : 0 < a) :
-- imply
  ContinuousOn (sctMeanfieldIntegratedError d n h) (Icc a b) := by
-- proof
  apply StatMech.Sharpness.continuousOn_sctMeanfieldIntegratedError d n h hh ha

/--
[sctMeanfieldGDeriv_le_integratedError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma sctMeanfieldGDeriv_le_integratedError_eq
  {d n : ℕ}
-- given
  (beta h : ℝ)
  (hn : 1 ≤ n)
  (hbdd : BddAbove (tildeBetaCIsingSet d))
  (habove : tildeBetaCIsing d < beta)
  (hh : 0 < h) :
-- imply
  sctMeanfieldGDeriv d n h beta ≤ sctMeanfieldIntegratedError d n h beta := by
-- proof
  apply StatMech.Sharpness.sctMeanfieldGDeriv_le_integratedError beta h hn hbdd habove hh

/--
[sctMeanfieldG_sub_le_integral_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma sctMeanfieldG_sub_le_integral_error_eq
  {d n : ℕ}
  {a b h : ℝ}
-- given
  (hn : 1 ≤ n)
  (hab : a ≤ b)
  (ha : 0 < a)
  (hh : 0 < h)
  (hbdd : BddAbove (tildeBetaCIsingSet d))
  (hcrit : tildeBetaCIsing d < a) :
-- imply
  sctMeanfieldG d n h b - sctMeanfieldG d n h a ≤ ∫ gamma in a..b, sctMeanfieldIntegratedError d n h gamma := by
-- proof
  apply StatMech.Sharpness.sctMeanfieldG_sub_le_integral_error hn hab ha hh hbdd hcrit

/--
[sctBoundaryCovarianceError_le_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma sctBoundaryCovarianceError_le_uniform_eq
  {d n : ℕ}
-- given
  (beta h : ℝ)
  (hn : 1 ≤ n)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  sctBoundaryCovarianceError d beta h n ≤ (2 * d : ℝ) / (beta * h) := by
-- proof
  apply StatMech.Sharpness.sctBoundaryCovarianceError_le_uniform beta h hn hbeta hh

/--
[sctMeanfieldIntegratedError_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma sctMeanfieldIntegratedError_tendsto_zero_eq
  {d : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (fun k : ℕ => sctMeanfieldIntegratedError d (k + 1) h beta) atTop (nhds 0) := by
-- proof
  apply StatMech.Sharpness.sctMeanfieldIntegratedError_tendsto_zero d beta h hbeta hh

/--
[norm_sctMeanfieldIntegratedError_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma norm_sctMeanfieldIntegratedError_le_eq
  {d n : ℕ}
  {a b h beta : ℝ}
-- given
  (hn : 1 ≤ n)
  (hab : a ≤ beta)
  (hbetab : beta ≤ b)
  (ha : 0 < a)
  (hh : 0 < h) :
-- imply
  ‖sctMeanfieldIntegratedError d n h beta‖ ≤ 2 * b + 2 * b ^ 2 * ((2 * d : ℝ) / (a * h)) := by
-- proof
  apply StatMech.Sharpness.norm_sctMeanfieldIntegratedError_le hn hab hbetab ha hh

/--
[sctMeanfieldIntegratedError_integral_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma sctMeanfieldIntegratedError_integral_tendsto_zero_eq
  {d : ℕ}
  {a b h : ℝ}
-- given
  (hab : a ≤ b)
  (ha : 0 < a)
  (hh : 0 < h) :
-- imply
  Tendsto (fun k : ℕ => ∫ beta in a..b, sctMeanfieldIntegratedError d (k + 1) h beta) atTop (nhds 0) := by
-- proof
  apply StatMech.Sharpness.sctMeanfieldIntegratedError_integral_tendsto_zero d hab ha hh

/--
[sctMeanfieldG_tendsto_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma sctMeanfieldG_tendsto_infinite_eq
  {d : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  Tendsto (fun k : ℕ => sctMeanfieldG d (k + 1) h beta) atTop (nhds (sctInfiniteMeanfieldG d h beta)) := by
-- proof
  apply StatMech.Sharpness.sctMeanfieldG_tendsto_infinite d beta h hbeta hh

/--
[sctInfiniteMeanfieldG_antitone_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma sctInfiniteMeanfieldG_antitone_above_eq
  {d : ℕ}
  {a b h : ℝ}
-- given
  (hab : a ≤ b)
  (ha : 0 < a)
  (hh : 0 < h)
  (hbdd : BddAbove (tildeBetaCIsingSet d))
  (hcrit : tildeBetaCIsing d < a) :
-- imply
  sctInfiniteMeanfieldG d h b ≤ sctInfiniteMeanfieldG d h a := by
-- proof
  apply StatMech.Sharpness.sctInfiniteMeanfieldG_antitone_above d hab ha hh hbdd hcrit

/--
[sctInfiniteFieldMag_meanfield_lower_bound_integrated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma sctInfiniteFieldMag_meanfield_lower_bound_integrated_eq
  {d : ℕ}
  {beta h : ℝ}
-- given
  (hbdd : BddAbove (tildeBetaCIsingSet d))
  (hcrit : 0 < tildeBetaCIsing d)
  (hbeta : tildeBetaCIsing d ≤ beta)
  (hh : 0 < h) :
-- imply
  Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤ sctInfiniteFieldMag d beta h := by
-- proof
  apply StatMech.Sharpness.sctInfiniteFieldMag_meanfield_lower_bound_integrated d hbdd hcrit hbeta hh

/--
[sctZeroPlus_meanfield_lower_bound_integrated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingIntegrated.lean)
-/
@[path]
private lemma sctZeroPlus_meanfield_lower_bound_integrated_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbdd : BddAbove (tildeBetaCIsingSet d))
  (hcrit : 0 < tildeBetaCIsing d)
  (hbeta : tildeBetaCIsing d ≤ beta) :
-- imply
  Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤ sctZeroPlusMag d beta := by
-- proof
  apply StatMech.Sharpness.sctZeroPlus_meanfield_lower_bound_integrated d hbdd hcrit hbeta


-- created on 2026-10-23
