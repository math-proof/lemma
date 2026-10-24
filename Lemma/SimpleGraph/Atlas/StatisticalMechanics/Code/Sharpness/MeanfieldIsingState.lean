import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.MeanfieldIsingState
open MeasureTheory Real Set Filter Topology StatMech StatMech.Sharpness


/--
[sct_bondFinsetInternal_eq_map_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sct_bondFinsetInternal_eq_map_edgeFinset_eq
  {d n : ℕ} :
-- imply
  bondFinsetInternal d n = (sctBoxGraph d n).edgeFinset.map (Function.Embedding.subtype (fun x : Site d => x ∈ box d n)).sym2Map := by
-- proof
  apply StatMech.Sharpness.sct_bondFinsetInternal_eq_map_edgeFinset d n

/--
[sct_internal_bond_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sct_internal_bond_sum_eq_eq
  {d n : ℕ}
  {tau : ConfigSpace (sctBox d n)} :
-- imply
  (∑ e ∈ bondFinsetInternal d n, bond (glue (minusField d) tau) e) = ∑ e ∈ (sctBoxGraph d n).edgeFinset, bond tau e := by
-- proof
  apply StatMech.Sharpness.sct_internal_bond_sum_eq d n tau

/--
[sct_internal_spin_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sct_internal_spin_sum_eq_eq
  {d n : ℕ}
  {tau : ConfigSpace (sctBox d n)} :
-- imply
  (∑ x ∈ Ising.boxFinset d n, spin (glue (minusField d) tau) x) = ∑ x : sctBox d n, spin tau x := by
-- proof
  apply StatMech.Sharpness.sct_internal_spin_sum_eq d n tau

/--
[sct_fvWeight_eq_isingWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sct_fvWeight_eq_isingWeight_eq
  {d n : ℕ}
  {tau : ConfigSpace (sctBox d n)}
-- given
  (beta h : ℝ) :
-- imply
  fvWeight (minusField d) n (bondFinsetInternal d n) beta h tau = isingWeight (sctBoxGraph d n) beta h tau := by
-- proof
  apply StatMech.Sharpness.sct_fvWeight_eq_isingWeight d n beta h tau

/--
[sct_fvZ_eq_isingZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sct_fvZ_eq_isingZ_eq
  {d n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  fvZ (minusField d) n (bondFinsetInternal d n) beta h = isingZ (sctBoxGraph d n) beta h := by
-- proof
  apply StatMech.Sharpness.sct_fvZ_eq_isingZ d n beta h

/--
[sct_fvProb_eq_isingProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sct_fvProb_eq_isingProb_eq
  {d n : ℕ}
  {tau : ConfigSpace (sctBox d n)}
-- given
  (beta h : ℝ) :
-- imply
  fvProb (minusField d) n (bondFinsetInternal d n) beta h tau = isingProb (sctBoxGraph d n) beta h tau := by
-- proof
  apply StatMech.Sharpness.sct_fvProb_eq_isingProb d n beta h tau

/--
[sct_integral_freeMeasure_eq_originMag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sct_integral_freeMeasure_eq_originMag_eq
  {d n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  ∫ omega, spin omega (Percolation.origin d) ∂(freeMeasure d n beta h : Measure (ConfigSpace (Site d))) = sctOriginMag d beta h n := by
-- proof
  apply StatMech.Sharpness.sct_integral_freeMeasure_eq_originMag d n beta h

/--
[sct_integral_freeState_eq_infiniteFieldMag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sct_integral_freeState_eq_infiniteFieldMag_eq
  {d : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  ∫ omega, spin omega (Percolation.origin d) ∂(freeState d beta h : Measure (ConfigSpace (Site d))) = sctInfiniteFieldMag d beta h := by
-- proof
  apply StatMech.Sharpness.sct_integral_freeState_eq_infiniteFieldMag d beta h hbeta hh

/--
[isingExpectation_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma isingExpectation_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (beta h : ℝ) :
-- imply
  isingExpectation G beta h f = expJ G.edgeFinset (fun _ => beta) (fun _ => beta * h) f := by
-- proof
  apply StatMech.Sharpness.isingExpectation_eq_expJ G beta h f

/--
[ghsiCovariance_const_eq_cov2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma ghsiCovariance_const_eq_cov2_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x : V}
-- given
  (beta h : ℝ) :
-- imply
  ghsiCovariance G (fun _ => beta) (fun _ => beta * h) o x = cov2 G beta h o x := by
-- proof
  apply StatMech.Sharpness.ghsiCovariance_const_eq_cov2 G beta h o x

/--
[ghsiDirectionalCovariance_const_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma ghsiDirectionalCovariance_const_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ ghsiDirectionalCovariance G (fun _ => beta) (fun _ => beta * h) (fun _ => beta) (fun s => spin s o) := by
-- proof
  apply StatMech.Sharpness.ghsiDirectionalCovariance_const_nonneg G beta h hbeta hh o

/--
[hasDerivAt_isingExpectation_spin_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma hasDerivAt_isingExpectation_spin_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (beta h : ℝ) :
-- imply
  HasDerivAt (fun u => isingExpectation G beta u (fun s => spin s o)) (ghsiDirectionalCovariance G (fun _ => beta) (fun _ => beta * h) (fun _ => beta) (fun s => spin s o)) h := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_isingExpectation_spin_field G beta h o

/--
[sctOriginMag_monotone_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sctOriginMag_monotone_field_eq
  {d n : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  MonotoneOn (fun h => sctOriginMag d beta h n) (Ici 0) := by
-- proof
  apply StatMech.Sharpness.sctOriginMag_monotone_field d n beta hbeta

/--
[sctInfiniteFieldMag_monotone_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sctInfiniteFieldMag_monotone_field_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  MonotoneOn (fun h => sctInfiniteFieldMag d beta h) (Ici 0) := by
-- proof
  apply StatMech.Sharpness.sctInfiniteFieldMag_monotone_field d beta hbeta

/--
[sctOriginMag_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sctOriginMag_nonneg_eq
  {d n : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ sctOriginMag d beta h n := by
-- proof
  apply StatMech.Sharpness.sctOriginMag_nonneg d n beta h hbeta hh

/--
[sctInfiniteFieldMag_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sctInfiniteFieldMag_nonneg_eq
  {d : ℕ}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ sctInfiniteFieldMag d beta h := by
-- proof
  apply StatMech.Sharpness.sctInfiniteFieldMag_nonneg d beta h hbeta hh

/--
[sctInfiniteFieldMag_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sctInfiniteFieldMag_le_one_eq
  {d : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  sctInfiniteFieldMag d beta h ≤ 1 := by
-- proof
  apply StatMech.Sharpness.sctInfiniteFieldMag_le_one d beta h

/--
[sctFieldToZero_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sctFieldToZero_pos_eq
  {n : ℕ} :
-- imply
  0 < sctFieldToZero n := by
-- proof
  apply StatMech.Sharpness.sctFieldToZero_pos n

/--
[sctFieldToZero_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sctFieldToZero_antitone_eq :
-- imply
  Antitone sctFieldToZero := by
-- proof
  apply StatMech.Sharpness.sctFieldToZero_antitone

/--
[sctInfiniteFieldMag_tendsto_zeroPlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sctInfiniteFieldMag_tendsto_zeroPlus_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Tendsto (fun n => sctInfiniteFieldMag d beta (sctFieldToZero n)) atTop (nhds (sctZeroPlusMag d beta)) := by
-- proof
  apply StatMech.Sharpness.sctInfiniteFieldMag_tendsto_zeroPlus d beta hbeta

/--
[sct_integral_freeState_tendsto_zeroPlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sct_integral_freeState_tendsto_zeroPlus_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Tendsto (fun n => ∫ omega, spin omega (Percolation.origin d) ∂(freeState d beta (sctFieldToZero n) : Measure (ConfigSpace (Site d)))) atTop (nhds (sctZeroPlusMag d beta)) := by
-- proof
  apply StatMech.Sharpness.sct_integral_freeState_tendsto_zeroPlus d beta hbeta

/--
[sctZeroPlus_meanfield_lower_bound_of_deriv_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingState.lean)
-/
@[path]
private lemma sctZeroPlus_meanfield_lower_bound_of_deriv_tendsto_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbdd : BddAbove (tildeBetaCIsingSet d))
  (hcrit : 0 < tildeBetaCIsing d)
  (hdiff : ∀ k : ℕ, ∀ gamma ∈ Ici (tildeBetaCIsing d), DifferentiableAt ℝ (fun b => (sctInfiniteFieldMag d b (sctFieldToZero k)) ^ 2) gamma)
  (hderiv : ∀ k : ℕ, ∀ gamma ∈ Ioi (tildeBetaCIsing d), Tendsto (fun n : ℕ => deriv (fun b => (sctOriginMag d b (sctFieldToZero k) (n + 1)) ^ 2) gamma) atTop (nhds (deriv (fun b => (sctInfiniteFieldMag d b (sctFieldToZero k)) ^ 2) gamma)))
  (hbeta : tildeBetaCIsing d ≤ beta) :
-- imply
  Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤ sctZeroPlusMag d beta := by
-- proof
  apply StatMech.Sharpness.sctZeroPlus_meanfield_lower_bound_of_deriv_tendsto d hbdd hcrit hdiff hderiv hbeta


-- created on 2026-10-23
