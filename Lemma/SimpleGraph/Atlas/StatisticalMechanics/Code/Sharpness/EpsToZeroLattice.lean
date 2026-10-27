import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.EpsToZeroLattice
open Filter Topology Finset SimpleGraph StatMech StatMech.Sharpness


/--
[sct_expJ_const_eq_isingExpectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sct_expJ_const_eq_isingExpectation_eq
  {d n : ℕ}
  {f : ConfigSpace (sctBox d n) → ℝ}
-- given
  (beta h : ℝ) :
-- imply
  expJ (sctBoxGraph d n).edgeFinset (fun _ => beta) (fun _ => beta * h) f = isingExpectation (sctBoxGraph d n) beta h f := by
-- proof
  apply StatMech.Sharpness.sct_expJ_const_eq_isingExpectation d n beta h f

/--
[sct_fieldLine_inner_outer_eq_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sct_fieldLine_inner_outer_eq_const_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  ghsiFieldLine (sctInnerField d beta h n) (sctOuterDirection d n) (beta * h) = (fun _ => beta * h) := by
-- proof
  apply StatMech.Sharpness.sct_fieldLine_inner_outer_eq_const d beta h n

/--
[sct_fieldLine_inner_outer_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sct_fieldLine_inner_outer_zero_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  ghsiFieldLine (sctInnerField d beta h n) (sctOuterDirection d n) 0 = sctInnerField d beta h n := by
-- proof
  apply StatMech.Sharpness.sct_fieldLine_inner_outer_zero d beta h n

/--
[sctOuterDirection_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctOuterDirection_origin_eq
  {d n : ℕ} :
-- imply
  sctOuterDirection d n (sctBoxOrigin d n) = 0 := by
-- proof
  apply StatMech.Sharpness.sctOuterDirection_origin d n

/--
[sctOuterDirection_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctOuterDirection_nonneg_eq
  {d n : ℕ} :
-- imply
  ∀ x, 0 ≤ sctOuterDirection d n x := by
-- proof
  apply StatMech.Sharpness.sctOuterDirection_nonneg d n

/--
[sctInnerField_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctInnerField_nonneg_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  ∀ x, 0 ≤ sctInnerField d beta h n x := by
-- proof
  apply StatMech.Sharpness.sctInnerField_nonneg d beta h hbeta hh n

/--
[sct_ghsiCovariance_const_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sct_ghsiCovariance_const_eq_eq
  {d : ℕ}
  {n : ℕ}
  {x : sctBox d n}
-- given
  (beta h : ℝ) :
-- imply
  ghsiCovariance (sctBoxGraph d n) (fun _ => beta) (fun _ => beta * h) (sctBoxOrigin d n) x = sctBoxCovariance d beta h n x := by
-- proof
  apply StatMech.Sharpness.sct_ghsiCovariance_const_eq d beta h n x

/--
[sct_directionalCovariance_eq_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sct_directionalCovariance_eq_outer_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  ghsiDirectionalCovariance (sctBoxGraph d n) (fun _ => beta) (fun _ => beta * h) (sctOuterDirection d n) (fun s => spin s (sctBoxOrigin d n)) = sctOuterCovarianceSum d beta h n := by
-- proof
  apply StatMech.Sharpness.sct_directionalCovariance_eq_outer d beta h n

/--
[sctOuterCovarianceSum_le_secant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctOuterCovarianceSum_le_secant_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  sctOuterCovarianceSum d beta h n ≤ (sctOriginMag d beta h n - sctInnerFieldMag d beta h n) / (beta * h) := by
-- proof
  apply StatMech.Sharpness.sctOuterCovarianceSum_le_secant d beta h hbeta hh n

/--
[sctOriginMag_pred_le_innerFieldMag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctOriginMag_pred_le_innerFieldMag_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  sctOriginMag d beta h (n - 1) ≤ sctInnerFieldMag d beta h n := by
-- proof
  apply StatMech.Sharpness.sctOriginMag_pred_le_innerFieldMag d beta h hbeta hh n

/--
[sctOuterCovarianceSum_le_magDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctOuterCovarianceSum_le_magDiff_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  sctOuterCovarianceSum d beta h n ≤ (sctOriginMag d beta h n - sctOriginMag d beta h (n - 1)) / (beta * h) := by
-- proof
  apply StatMech.Sharpness.sctOuterCovarianceSum_le_magDiff d beta h hbeta hh n

/--
[sctBoxCovariance_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctBoxCovariance_nonneg_eq
  {d : ℕ}
  {n : ℕ}
  {x : sctBox d n}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ sctBoxCovariance d beta h n x := by
-- proof
  apply StatMech.Sharpness.sctBoxCovariance_nonneg d beta h hbeta hh n x

/--
[sctBoundaryCovarianceError_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctBoundaryCovarianceError_nonneg_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ sctBoundaryCovarianceError d beta h n := by
-- proof
  apply StatMech.Sharpness.sctBoundaryCovarianceError_nonneg d beta h hbeta hh n

/--
[sctExteriorNeighbours_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctExteriorNeighbours_card_le_eq
  {d n : ℕ}
  {x : Site d} :
-- imply
  (sctExteriorNeighbours d n x).card ≤ 2 * d := by
-- proof
  apply StatMech.Sharpness.sctExteriorNeighbours_card_le d n x

/--
[sct_adj_mem_box_of_mem_box_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sct_adj_mem_box_of_mem_box_pred_eq
  {d n : ℕ}
  {x y : Site d}
-- given
  (hn : 1 ≤ n)
  (hx : x ∈ box d (n - 1))
  (hxy : (hypercubicLattice d).Adj x y) :
-- imply
  y ∈ box d n := by
-- proof
  apply StatMech.Sharpness.sct_adj_mem_box_of_mem_box_pred hn hx hxy

/--
[sctExteriorNeighbours_eq_empty_of_mem_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctExteriorNeighbours_eq_empty_of_mem_pred_eq
  {d n : ℕ}
  {x : Site d}
-- given
  (hn : 1 ≤ n)
  (hx : x ∈ box d (n - 1)) :
-- imply
  sctExteriorNeighbours d n x = ∅ := by
-- proof
  apply StatMech.Sharpness.sctExteriorNeighbours_eq_empty_of_mem_pred hn hx

/--
[sctBoundaryCovarianceError_outerLayer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctBoundaryCovarianceError_outerLayer_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ)
  (hn : 1 ≤ n) :
-- imply
  sctBoundaryCovarianceError d beta h n = ∑ x : sctBox d n, if x.1 ∈ box d (n - 1) then 0 else ((sctExteriorNeighbours d n x.1).card : ℝ) * sctBoxCovariance d beta h n x := by
-- proof
  apply StatMech.Sharpness.sctBoundaryCovarianceError_outerLayer d beta h n hn

/--
[sctBoundaryCovarianceError_le_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctBoundaryCovarianceError_le_outer_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hn : 1 ≤ n) :
-- imply
  sctBoundaryCovarianceError d beta h n ≤ (2 * d : ℝ) * sctOuterCovarianceSum d beta h n := by
-- proof
  apply StatMech.Sharpness.sctBoundaryCovarianceError_le_outer d beta h hbeta hh n hn

/--
[sctOriginMag_tendsto_iSup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctOriginMag_tendsto_iSup_eq
  {d : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  Tendsto (sctOriginMag d beta h) atTop (nhds (⨆ n : ℕ, sctOriginMag d beta h n)) := by
-- proof
  apply StatMech.Sharpness.sctOriginMag_tendsto_iSup d beta h hbeta hh

/--
[sctOuterCovarianceSum_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctOuterCovarianceSum_tendsto_zero_eq
  {d : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (sctOuterCovarianceSum d beta h) atTop (nhds 0) := by
-- proof
  apply StatMech.Sharpness.sctOuterCovarianceSum_tendsto_zero d beta h hbeta hh

/--
[sctBoundaryCovarianceError_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/EpsToZeroLattice.lean)
-/
@[path]
private lemma sctBoundaryCovarianceError_tendsto_zero_eq
  {d : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  Tendsto (sctBoundaryCovarianceError d beta h) atTop (nhds 0) := by
-- proof
  apply StatMech.Sharpness.sctBoundaryCovarianceError_tendsto_zero d beta h hbeta hh


-- created on 2026-10-23
