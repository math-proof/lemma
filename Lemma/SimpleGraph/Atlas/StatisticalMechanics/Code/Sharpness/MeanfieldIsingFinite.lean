import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingFinite.Part10
open Finset SimpleGraph StatMech StatMech.Sharpness


/--
[mem_sctCutSites](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma mem_sctCutSites_eq
  {d n : ℕ}
  {T : Finset (sctBox d n)}
  {x : sctBox d n} :
-- imply
  x.1 ∈ sctCutSites T ↔ x ∈ T := by
-- proof
  apply StatMech.Sharpness.mem_sctCutSites

/--
[sctCutVertexEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctCutVertexEquiv_adj_eq
  {d n : ℕ}
  {T : Finset (sctBox d n)}
-- given
  (a b : {x : sctBox d n // x ∈ T}) :
-- imply
  ((sctBoxGraph d n).comap (Subtype.val : {x : sctBox d n // x ∈ T} → sctBox d n)).Adj a b ↔ (graphS d (sctCutSites T)).Adj (sctCutVertexEquiv T a) (sctCutVertexEquiv T b) := by
-- proof
  apply StatMech.Sharpness.sctCutVertexEquiv_adj T a b

/--
[sct_localCorr_eq_corrOriginInner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_localCorr_eq_corrOriginInner_eq
  {d n : ℕ}
  {beta : ℝ}
  {T : Finset (sctBox d n)}
  {x : sctBox d n}
-- given
  (ho : sctBoxOrigin d n ∈ T)
  (hx : x ∈ T)
  (hox : sctBoxOrigin d n ≠ x) :
-- imply
  expectationJ (sctBoxGraph d n) beta (couplingIn (fun _ => 1) T) {sctBoxOrigin d n, x} = corrOriginInner d beta (sctCutSites T) x.1 := by
-- proof
  apply StatMech.Sharpness.sct_localCorr_eq_corrOriginInner beta T ho hx hox

/--
[sct_corrOriginInner_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_corrOriginInner_origin_eq
  {d n : ℕ}
  {beta : ℝ}
  {T : Finset (sctBox d n)}
-- given
  (ho : sctBoxOrigin d n ∈ T) :
-- imply
  corrOriginInner d beta (sctCutSites T) (origin d) = 1 := by
-- proof
  apply StatMech.Sharpness.sct_corrOriginInner_origin beta T ho

/--
[sct_normalizedDeltaLowerMass_eq_orientedCutMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_normalizedDeltaLowerMass_eq_orientedCutMass_eq
  {d n : ℕ}
  {x y : sctBox d n}
-- given
  (beta h : ℝ)
  (hox : sctBoxOrigin d n ≠ x) :
-- imply
  (currentSum (withGhost (sctBoxGraph d n)) beta (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 * isingDeltaLowerMass (withGhost (sctBoxGraph d n)) beta (ghostCoupling h beta (fun _ => 1)) (some (sctBoxOrigin d n)) (some x) (some y) none = sctOrientedCutMass d beta h n x y := by
-- proof
  apply StatMech.Sharpness.sct_normalizedDeltaLowerMass_eq_orientedCutMass beta h hox

/--
[sct_normalizedDeltaSelfLowerMass_eq_orientedCutMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_normalizedDeltaSelfLowerMass_eq_orientedCutMass_eq
  {d n : ℕ}
  {y : sctBox d n}
-- given
  (beta h : ℝ) :
-- imply
  (currentSum (withGhost (sctBoxGraph d n)) beta (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 * isingDeltaSelfLowerMass (withGhost (sctBoxGraph d n)) beta (ghostCoupling h beta (fun _ => 1)) (some (sctBoxOrigin d n)) (some y) none = sctOrientedCutMass d beta h n (sctBoxOrigin d n) y := by
-- proof
  apply StatMech.Sharpness.sct_normalizedDeltaSelfLowerMass_eq_orientedCutMass beta h y

/--
[sctLatticeC_le_siteRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctLatticeC_le_siteRatio_eq
  {d n : ℕ}
  {y : sctBox d n}
-- given
  (beta h : ℝ) :
-- imply
  sctLatticeC d beta h n ≤ sctOriginMag d beta h n / sctBoxMag d beta h n y := by
-- proof
  apply StatMech.Sharpness.sctLatticeC_le_siteRatio beta h y

/--
[sctLatticeC_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctLatticeC_nonneg_eq
  {d n : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  0 ≤ sctLatticeC d beta h n := by
-- proof
  apply StatMech.Sharpness.sctLatticeC_nonneg beta h hbeta hh

/--
[sctLatticeC_mul_siteMag_le_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctLatticeC_mul_siteMag_le_origin_eq
  {d n : ℕ}
  {y : sctBox d n}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  sctLatticeC d beta h n * sctBoxMag d beta h n y ≤ sctOriginMag d beta h n := by
-- proof
  apply StatMech.Sharpness.sctLatticeC_mul_siteMag_le_origin beta h hbeta hh y

/--
[sct_nonincidentBondDelta_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_nonincidentBondDelta_bound_eq
  {d n : ℕ}
  {x y : sctBox d n}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hox : sctBoxOrigin d n ≠ x)
  (hoy : sctBoxOrigin d n ≠ y)
  (hxy : x ≠ y) :
-- imply
  (currentSum (withGhost (sctBoxGraph d n)) beta (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 * (sctOriginMag d beta h n * HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h (sctBoxOrigin d n) s(x, y)) ≥ sctLatticeC d beta h n * (sctOrientedCutMass d beta h n x y + sctOrientedCutMass d beta h n y x) := by
-- proof
  apply StatMech.Sharpness.sct_nonincidentBondDelta_bound beta h hbeta hh hox hoy hxy

/--
[sct_incidentBondDelta_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_incidentBondDelta_bound_eq
  {d n : ℕ}
  {y : sctBox d n}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hoy : sctBoxOrigin d n ≠ y) :
-- imply
  (currentSum (withGhost (sctBoxGraph d n)) beta (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 * (sctOriginMag d beta h n * HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h (sctBoxOrigin d n) s(sctBoxOrigin d n, y)) ≥ sctLatticeC d beta h n * sctOrientedCutMass d beta h n (sctBoxOrigin d n) y := by
-- proof
  apply StatMech.Sharpness.sct_incidentBondDelta_bound beta h hbeta hh y hoy

/--
[sctEdgeCutMass_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctEdgeCutMass_mk_eq
  {d : ℕ}
  {n : ℕ}
  {x y : sctBox d n}
-- given
  (beta h : ℝ) :
-- imply
  sctEdgeCutMass d beta h n s(x, y) = sctOrientedCutMass d beta h n x y + sctOrientedCutMass d beta h n y x := by
-- proof
  apply StatMech.Sharpness.sctEdgeCutMass_mk d beta h n x y

/--
[sctOrientedCutMass_to_origin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctOrientedCutMass_to_origin_zero_eq
  {d n : ℕ}
  {x : sctBox d n}
-- given
  (beta h : ℝ) :
-- imply
  sctOrientedCutMass d beta h n x (sctBoxOrigin d n) = 0 := by
-- proof
  apply StatMech.Sharpness.sctOrientedCutMass_to_origin_zero beta h x

/--
[sct_bondDelta_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_bondDelta_bound_eq
  {d n : ℕ}
  {e : Sym2 (sctBox d n)}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (he : e ∈ (sctBoxGraph d n).edgeFinset) :
-- imply
  (currentSum (withGhost (sctBoxGraph d n)) beta (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 * (sctOriginMag d beta h n * HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h (sctBoxOrigin d n) e) ≥ sctLatticeC d beta h n * sctEdgeCutMass d beta h n e := by
-- proof
  apply StatMech.Sharpness.sct_bondDelta_bound beta h hbeta hh e he

/--
[sct_sum_bondDelta_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_sum_bondDelta_bound_eq
  {d n : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h) :
-- imply
  (currentSum (withGhost (sctBoxGraph d n)) beta (ghostCoupling h beta (fun _ => 1)) ∅)⁻¹ ^ 2 * (sctOriginMag d beta h n * ∑ e ∈ (sctBoxGraph d n).edgeFinset, HcovAssembly.hcaBondDelta (sctBoxGraph d n) beta h (sctBoxOrigin d n) e) ≥ sctLatticeC d beta h n * ∑ e ∈ (sctBoxGraph d n).edgeFinset, sctEdgeCutMass d beta h n e := by
-- proof
  apply StatMech.Sharpness.sct_sum_bondDelta_bound beta h hbeta hh

/--
[sctEdgeCutMass_eq_sum_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctEdgeCutMass_eq_sum_boundary_eq
  {d n : ℕ}
  {e : Sym2 (sctBox d n)}
-- given
  (beta h : ℝ) :
-- imply
  sctEdgeCutMass d beta h n e = ∑ T : Finset (sctBox d n), if sctBoxOrigin d n ∈ T then sctEdgeBoundaryCorr beta T e * sctCurrentCutMass d beta h n T else 0 := by
-- proof
  apply StatMech.Sharpness.sctEdgeCutMass_eq_sum_boundary beta h e

/--
[sct_sum_edgeCutMass_eq_sum_internalBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_sum_edgeCutMass_eq_sum_internalBoundary_eq
  {d n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  (∑ e ∈ (sctBoxGraph d n).edgeFinset, sctEdgeCutMass d beta h n e) = ∑ T : Finset (sctBox d n), if sctBoxOrigin d n ∈ T then sctInternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T else 0 := by
-- proof
  apply StatMech.Sharpness.sct_sum_edgeCutMass_eq_sum_internalBoundary beta h

/--
[sctCutSites_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctCutSites_subset_box_eq
  {d n : ℕ}
  {T : Finset (sctBox d n)} :
-- imply
  (sctCutSites T : Set (Site d)) ⊆ box d n := by
-- proof
  apply StatMech.Sharpness.sctCutSites_subset_box T

/--
[sctBoxize_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctBoxize_val_eq
  {d n : ℕ}
  {z : Site d}
-- given
  (hz : z ∈ box d n) :
-- imply
  (sctBoxize d n z).1 = z := by
-- proof
  apply StatMech.Sharpness.sctBoxize_val hz

/--
[sctInternalBoundaryCorr_eq_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctInternalBoundaryCorr_eq_ambient_eq
  {d n : ℕ}
  {beta : ℝ}
  {T : Finset (sctBox d n)} :
-- imply
  sctInternalBoundaryCorr d beta n T = ∑ e ∈ (boundaryEdges d (sctCutSites T)).filter (fun e => e.2 ∈ box d n), corrOriginInner d beta (sctCutSites T) e.1 := by
-- proof
  apply StatMech.Sharpness.sctInternalBoundaryCorr_eq_ambient beta T

/--
[sct_boundaryCorr_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_boundaryCorr_split_eq
  {d n : ℕ}
  {beta : ℝ}
  {T : Finset (sctBox d n)} :
-- imply
  (∑ e ∈ boundaryEdges d (sctCutSites T), corrOriginInner d beta (sctCutSites T) e.1) = sctInternalBoundaryCorr d beta n T + sctExternalBoundaryCorr d beta n T := by
-- proof
  apply StatMech.Sharpness.sct_boundaryCorr_split beta T

/--
[sct_phiIsing_eq_tanh_mul_boundaryCorr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_phiIsing_eq_tanh_mul_boundaryCorr_eq
  {d n : ℕ}
  {beta : ℝ}
  {T : Finset (sctBox d n)} :
-- imply
  phiIsing d beta (sctCutSites T) = Real.tanh beta * ∑ e ∈ boundaryEdges d (sctCutSites T), corrOriginInner d beta (sctCutSites T) e.1 := by
-- proof
  apply StatMech.Sharpness.sct_phiIsing_eq_tanh_mul_boundaryCorr beta T

/--
[tanh_le_self_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma tanh_le_self_of_nonneg_eq
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Real.tanh beta ≤ beta := by
-- proof
  apply StatMech.Sharpness.tanh_le_self_of_nonneg hbeta

/--
[sct_sum_currentCutMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_sum_currentCutMass_eq
  {d n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  (∑ T : Finset (sctBox d n), if sctBoxOrigin d n ∈ T then sctCurrentCutMass d beta h n T else 0) = 1 - (sctOriginMag d beta h n) ^ 2 := by
-- proof
  apply StatMech.Sharpness.sct_sum_currentCutMass beta h

/--
[sct_internalBoundaryMass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_internalBoundaryMass_lower_eq
  {d n : ℕ}
-- given
  (beta h infphi : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 ≤ h)
  (hinf : ∀ S : Finset (Site d), origin d ∈ S → infphi ≤ phiIsing d beta S) :
-- imply
  (∑ T : Finset (sctBox d n), if sctBoxOrigin d n ∈ T then sctInternalBoundaryCorr d beta n T * sctCurrentCutMass d beta h n T else 0) ≥ (1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) - sctCurrentBoundaryError d beta h n := by
-- proof
  apply StatMech.Sharpness.sct_internalBoundaryMass_lower beta h infphi hbeta hh hinf

/--
[sct_finite_meanfield_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_finite_meanfield_inequality_eq
  {d n : ℕ}
-- given
  (beta h infphi : ℝ)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hinf : ∀ S : Finset (Site d), origin d ∈ S → infphi ≤ phiIsing d beta S) :
-- imply
  deriv (fun b => (sctOriginMag d b h n) ^ 2) beta ≥ 2 * sctLatticeC d beta h n * ((1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) - sctCurrentBoundaryError d beta h n) := by
-- proof
  apply StatMech.Sharpness.sct_finite_meanfield_inequality beta h infphi hbeta hh hinf

/--
[mem_sctExternalBoxPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma mem_sctExternalBoxPairs_eq
  {d n : ℕ}
  {p : sctBox d n × Site d} :
-- imply
  p ∈ sctExternalBoxPairs d n ↔ p.2 ∈ sctExteriorNeighbours d n p.1.1 := by
-- proof
  apply StatMech.Sharpness.mem_sctExternalBoxPairs

/--
[sctExternalBoundaryCorr_eq_sum_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctExternalBoundaryCorr_eq_sum_vertices_eq
  {d n : ℕ}
  {beta : ℝ}
  {T : Finset (sctBox d n)} :
-- imply
  sctExternalBoundaryCorr d beta n T = ∑ x : sctBox d n, if x ∈ T then ((sctExteriorNeighbours d n x.1).card : ℝ) * corrOriginInner d beta (sctCutSites T) x.1 else 0 := by
-- proof
  apply StatMech.Sharpness.sctExternalBoundaryCorr_eq_sum_vertices beta T

/--
[sct_sum_cutCorr_eq_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_sum_cutCorr_eq_covariance_eq
  {d n : ℕ}
  {x : sctBox d n}
-- given
  (beta h : ℝ)
  (hox : sctBoxOrigin d n ≠ x) :
-- imply
  (∑ T : Finset (sctBox d n), if sctBoxOrigin d n ∈ T ∧ x ∈ T then corrOriginInner d beta (sctCutSites T) x.1 * sctCurrentCutMass d beta h n T else 0) = sctBoxCovariance d beta h n x := by
-- proof
  apply StatMech.Sharpness.sct_sum_cutCorr_eq_covariance beta h x hox

/--
[sctCurrentBoundaryError_eq_boundaryCovarianceError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sctCurrentBoundaryError_eq_boundaryCovarianceError_eq
  {d n : ℕ}
-- given
  (beta h : ℝ)
  (hn : 1 ≤ n) :
-- imply
  sctCurrentBoundaryError d beta h n = sctBoundaryCovarianceError d beta h n := by
-- proof
  apply StatMech.Sharpness.sctCurrentBoundaryError_eq_boundaryCovarianceError beta h hn

/--
[sct_finite_meanfield_inequality_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingFinite.lean)
-/
@[path]
private lemma sct_finite_meanfield_inequality_concrete_eq
  {d n : ℕ}
-- given
  (beta h infphi : ℝ)
  (hn : 1 ≤ n)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hinf : ∀ S : Finset (Site d), origin d ∈ S → infphi ≤ phiIsing d beta S) :
-- imply
  deriv (fun b => (sctOriginMag d b h n) ^ 2) beta ≥ 2 * sctLatticeC d beta h n * ((1 / beta) * (infphi * (1 - (sctOriginMag d beta h n) ^ 2)) - sctBoundaryCovarianceError d beta h n) := by
-- proof
  apply StatMech.Sharpness.sct_finite_meanfield_inequality_concrete beta h infphi hn hbeta hh hinf


-- created on 2026-10-23
