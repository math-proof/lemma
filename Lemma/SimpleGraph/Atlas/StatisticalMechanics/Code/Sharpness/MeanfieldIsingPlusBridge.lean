import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.MeanfieldIsingPlusBridge
open MeasureTheory Real Set Filter Topology StatMech StatMech.Sharpness


/--
[sct_boundaryBond_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_boundaryBond_mono_eq
  {d n : ℕ}
  {e : Sym2 (Site d)}
  {a b : {x // x ∈ box d n} → Bool}
-- given
  (heT : e ∈ bondFinsetTouch d n)
  (heI : e ∉ bondFinsetInternal d n)
  (hab : a ≤ b) :
-- imply
  bond (glue (plusField d) a) e ≤ bond (glue (plusField d) b) e := by
-- proof
  apply StatMech.Sharpness.sct_boundaryBond_mono heT heI hab

/--
[sct_fvEnergy_internal_touch_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_fvEnergy_internal_touch_cross_eq
  {d n : ℕ}
-- given
  (h : ℝ)
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  fvEnergy (plusField d) n (bondFinsetInternal d n) h (a ⊓ b) + fvEnergy (plusField d) n (bondFinsetTouch d n) h (a ⊔ b) ≤ fvEnergy (plusField d) n (bondFinsetInternal d n) h a + fvEnergy (plusField d) n (bondFinsetTouch d n) h b := by
-- proof
  apply StatMech.Sharpness.sct_fvEnergy_internal_touch_cross h a b

/--
[sct_fvWeight_internal_touch_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_fvWeight_internal_touch_cross_eq
  {d n : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight (plusField d) n (bondFinsetInternal d n) β h a * fvWeight (plusField d) n (bondFinsetTouch d n) β h b ≤ fvWeight (plusField d) n (bondFinsetInternal d n) β h (a ⊓ b) * fvWeight (plusField d) n (bondFinsetTouch d n) β h (a ⊔ b) := by
-- proof
  apply StatMech.Sharpness.sct_fvWeight_internal_touch_cross hβ h a b

/--
[sct_fvProb_internal_touch_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_fvProb_internal_touch_cross_eq
  {d n : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (a b : {x // x ∈ box d n} → Bool) :
-- imply
  fvProb (plusField d) n (bondFinsetInternal d n) β h a * fvProb (plusField d) n (bondFinsetTouch d n) β h b ≤ fvProb (plusField d) n (bondFinsetInternal d n) β h (a ⊓ b) * fvProb (plusField d) n (bondFinsetTouch d n) β h (a ⊔ b) := by
-- proof
  apply StatMech.Sharpness.sct_fvProb_internal_touch_cross hβ h a b

/--
[sct_fvEnergy_internal_boundary_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_fvEnergy_internal_boundary_indep_eq
  {d n : ℕ}
  {eta eta' : ConfigSpace (Site d)}
-- given
  (h : ℝ)
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  fvEnergy eta n (bondFinsetInternal d n) h tau = fvEnergy eta' n (bondFinsetInternal d n) h tau := by
-- proof
  apply StatMech.Sharpness.sct_fvEnergy_internal_boundary_indep eta eta' h tau

/--
[sct_fvProb_internal_boundary_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_fvProb_internal_boundary_indep_eq
  {d n : ℕ}
  {eta eta' : ConfigSpace (Site d)}
-- given
  (beta h : ℝ)
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  fvProb eta n (bondFinsetInternal d n) beta h tau = fvProb eta' n (bondFinsetInternal d n) beta h tau := by
-- proof
  apply StatMech.Sharpness.sct_fvProb_internal_boundary_indep eta eta' beta h tau

/--
[sct_fvProb_free_le_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_fvProb_free_le_plus_eq
  {d n : ℕ}
  {beta : ℝ}
  {A : Set (ConfigSpace {x // x ∈ box d n})}
-- given
  (hbeta : 0 ≤ beta)
  (h : ℝ)
  (hA : IsIncreasing A) :
-- imply
  (∑ tau, A.indicator (fun _ => (1 : ℝ)) tau * fvProb (minusField d) n (bondFinsetInternal d n) beta h tau) ≤ ∑ tau, A.indicator (fun _ => (1 : ℝ)) tau * fvProb (plusField d) n (bondFinsetTouch d n) beta h tau := by
-- proof
  apply StatMech.Sharpness.sct_fvProb_free_le_plus hbeta h hA

/--
[sct_fvMeasure_free_le_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_fvMeasure_free_le_plus_eq
  {d n : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (h : ℝ) :
-- imply
  (fvMeasure (minusField d) n (bondFinsetInternal d n) beta h) ≼ fvMeasure (plusField d) n (bondFinsetTouch d n) beta h := by
-- proof
  apply StatMech.Sharpness.sct_fvMeasure_free_le_plus hbeta h

/--
[sct_isIncreasing_spinUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_isIncreasing_spinUp_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  IsIncreasing {omega : ConfigSpace (Site d) | omega x = true} := by
-- proof
  apply StatMech.Sharpness.sct_isIncreasing_spinUp x

/--
[sct_integral_spin_eq_two_siteProb_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_integral_spin_eq_two_siteProb_sub_one_eq
  {d : ℕ}
  {x : Site d}
  {mu : ProbabilityMeasure (ConfigSpace (Site d))} :
-- imply
  (∫ omega, spin omega x ∂(mu : Measure (ConfigSpace (Site d)))) = 2 * (mu : Measure (ConfigSpace (Site d))).real {omega | omega x = true} - 1 := by
-- proof
  apply StatMech.Sharpness.sct_integral_spin_eq_two_siteProb_sub_one x mu

/--
[sct_freeMeasure_real_le_plusMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_freeMeasure_real_le_plusMeasure_eq
  {d n : ℕ}
  {beta : ℝ}
  {A : Set (ConfigSpace (Site d))}
-- given
  (hbeta : 0 ≤ beta)
  (h : ℝ)
  (hAmeas : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  (freeMeasure d n beta h : Measure (ConfigSpace (Site d))).real A ≤ (plusMeasure d n beta h : Measure (ConfigSpace (Site d))).real A := by
-- proof
  apply StatMech.Sharpness.sct_freeMeasure_real_le_plusMeasure hbeta h hAmeas hAinc

/--
[sct_continuous_fvEnergy_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_continuous_fvEnergy_field_eq
  {d n : ℕ}
  {eta : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
-- given
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun h => fvEnergy eta n B h tau) := by
-- proof
  apply StatMech.Sharpness.sct_continuous_fvEnergy_field eta B tau

/--
[sct_continuous_fvWeight_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_continuous_fvWeight_field_eq
  {d n : ℕ}
  {eta : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
  {beta : ℝ}
-- given
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun h => fvWeight eta n B beta h tau) := by
-- proof
  apply StatMech.Sharpness.sct_continuous_fvWeight_field eta B beta tau

/--
[sct_continuous_fvZ_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_continuous_fvZ_field_eq
  {d n : ℕ}
  {eta : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
  {beta : ℝ} :
-- imply
  Continuous (fun h => fvZ eta n B beta h) := by
-- proof
  apply StatMech.Sharpness.sct_continuous_fvZ_field eta B beta

/--
[sct_continuous_fvProb_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_continuous_fvProb_field_eq
  {d n : ℕ}
  {eta : ConfigSpace (Site d)}
  {B : Finset (Sym2 (Site d))}
  {beta : ℝ}
-- given
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun h => fvProb eta n B beta h tau) := by
-- proof
  apply StatMech.Sharpness.sct_continuous_fvProb_field eta B beta tau

/--
[sct_continuous_plusMeasure_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_continuous_plusMeasure_real_eq
  {d n : ℕ}
  {beta : ℝ}
  {A : Set (ConfigSpace (Site d))}
-- given
  (hA : MeasurableSet A) :
-- imply
  Continuous (fun h => (plusMeasure d n beta h : Measure (ConfigSpace (Site d))).real A) := by
-- proof
  apply StatMech.Sharpness.sct_continuous_plusMeasure_real beta hA

/--
[sct_continuous_plusMeasure_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_continuous_plusMeasure_spin_eq
  {d n : ℕ}
  {beta : ℝ}
  {x : Site d} :
-- imply
  Continuous (fun h => ∫ omega, spin omega x ∂(plusMeasure d n beta h : Measure (ConfigSpace (Site d)))) := by
-- proof
  apply StatMech.Sharpness.sct_continuous_plusMeasure_spin beta x

/--
[sctFieldToZero_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sctFieldToZero_tendsto_zero_eq :
-- imply
  Tendsto sctFieldToZero atTop (nhds 0) := by
-- proof
  apply StatMech.Sharpness.sctFieldToZero_tendsto_zero

/--
[sctOriginMag_le_plusMeasure_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sctOriginMag_le_plusMeasure_spin_eq
  {d n m : ℕ}
  {beta h : ℝ}
-- given
  (hnm : n ≤ m)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  sctOriginMag d beta h m ≤ ∫ omega, spin omega (Percolation.origin d) ∂(plusMeasure d n beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Sharpness.sctOriginMag_le_plusMeasure_spin hnm hbeta hh

/--
[sctInfiniteFieldMag_le_plusMeasure_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sctInfiniteFieldMag_le_plusMeasure_spin_eq
  {d n : ℕ}
  {beta h : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  sctInfiniteFieldMag d beta h ≤ ∫ omega, spin omega (Percolation.origin d) ∂(plusMeasure d n beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Sharpness.sctInfiniteFieldMag_le_plusMeasure_spin hbeta hh

/--
[sctZeroPlusMag_le_plusMeasure_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sctZeroPlusMag_le_plusMeasure_spin_eq
  {d n : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  sctZeroPlusMag d beta ≤ ∫ omega, spin omega (Percolation.origin d) ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Sharpness.sctZeroPlusMag_le_plusMeasure_spin hbeta

/--
[sctZeroPlusMag_le_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sctZeroPlusMag_le_magnetization_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  sctZeroPlusMag d beta ≤ magnetization d beta := by
-- proof
  apply StatMech.Sharpness.sctZeroPlusMag_le_magnetization d hbeta

/--
[sct_magnetization_meanfield_lower_bound_integrated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldIsingPlusBridge.lean)
-/
@[path]
private lemma sct_magnetization_meanfield_lower_bound_integrated_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbdd : BddAbove (tildeBetaCIsingSet d))
  (hcrit : 0 < tildeBetaCIsing d)
  (hbeta : tildeBetaCIsing d ≤ beta) :
-- imply
  Real.sqrt (1 - (tildeBetaCIsing d / beta) ^ 2) ≤ magnetization d beta := by
-- proof
  apply StatMech.Sharpness.sct_magnetization_meanfield_lower_bound_integrated d hbdd hcrit hbeta


-- created on 2026-10-23
