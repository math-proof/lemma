import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.IsingMinusTIFromPlacement
open MeasureTheory Filter Topology Set StatMech StatMech.Ising


/--
[gv_minusField_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma gv_minusField_le_eq
  {d : ℕ}
  {eta : ConfigSpace (Site d)} :
-- imply
  minusField d ≤ eta := by
-- proof
  apply StatMech.Ising.gv_minusField_le eta

/--
[gvMeasure_minusField_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma gvMeasure_minusField_le_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {beta : ℝ}
  {h : ℝ}
  {eta : ConfigSpace (Site d)}
  {A : Set (ConfigSpace (Site d))}
-- given
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hA : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  (gvMeasure (minusField d) S beta h).real A ≤ (gvMeasure eta S beta h).real A := by
-- proof
  apply StatMech.Ising.gvMeasure_minusField_le S hbeta hh eta hA hAinc

/--
[iptm_gv_crossbox_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_gv_crossbox_dom_eq
  {d : ℕ}
  {Sin Sout : Finset (Site d)}
  {beta : ℝ}
  {h : ℝ}
  {A : Set (ConfigSpace (Site d))}
-- given
  (hsub : Sin ⊆ Sout)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hAmeas : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  (gvMinusMeasure Sin beta h).real A ≤ (gvMinusMeasure Sout beta h).real A := by
-- proof
  apply StatMech.Ising.iptm_gv_crossbox_dom hsub hbeta hh hAmeas hAinc

/--
[iptm_gvMinusMeasure_eq_minusMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_gvMinusMeasure_eq_minusMeasure_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  gvMinusMeasure (boxFinset d n) beta h = (minusMeasure d n beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.iptm_gvMinusMeasure_eq_minusMeasure n beta h

/--
[iptm_gvGlue_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_gvGlue_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (tau : {x // x ∈ S} → Bool) :
-- imply
  shift g (gvGlue (minusField d) S tau) = gvGlue (minusField d) (S.image (fun x => g • x)) (fun y => tau ((iptp_transInteriorEquiv g S).symm y)) := by
-- proof
  apply StatMech.Ising.iptm_gvGlue_shift g S tau

/--
[iptm_gvEnergy_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_gvEnergy_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (h : ℝ)
  (tau : {x // x ∈ S} → Bool) :
-- imply
  gvEnergy (minusField d) (S.image (fun x => g • x)) h (fun y => tau ((iptp_transInteriorEquiv g S).symm y)) = gvEnergy (minusField d) S h tau := by
-- proof
  apply StatMech.Ising.iptm_gvEnergy_shift g S h tau

/--
[iptm_gvWeight_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_gvWeight_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (beta h : ℝ)
  (tau : {x // x ∈ S} → Bool) :
-- imply
  gvWeight (minusField d) (S.image (fun x => g • x)) beta h (fun y => tau ((iptp_transInteriorEquiv g S).symm y)) = gvWeight (minusField d) S beta h tau := by
-- proof
  apply StatMech.Ising.iptm_gvWeight_shift g S beta h tau

/--
[iptm_gvZ_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_gvZ_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (beta h : ℝ) :
-- imply
  gvZ (minusField d) (S.image (fun x => g • x)) beta h = gvZ (minusField d) S beta h := by
-- proof
  apply StatMech.Ising.iptm_gvZ_shift g S beta h

/--
[iptm_gvProb_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_gvProb_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (beta h : ℝ)
  (tau : {x // x ∈ S} → Bool) :
-- imply
  gvProb (minusField d) (S.image (fun x => g • x)) beta h (fun y => tau ((iptp_transInteriorEquiv g S).symm y)) = gvProb (minusField d) S beta h tau := by
-- proof
  apply StatMech.Ising.iptm_gvProb_shift g S beta h tau

/--
[iptm_gvMeasure_map_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_gvMeasure_map_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (beta h : ℝ) :
-- imply
  Measure.map (shift g) (gvMinusMeasure S beta h) = gvMinusMeasure (S.image (fun x => g • x)) beta h := by
-- proof
  apply StatMech.Ising.iptm_gvMeasure_map_shift g S beta h

/--
[iptm_gvMinus_real_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_gvMinus_real_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
  {T : Finset (Site d)}
-- given
  (beta h : ℝ) :
-- imply
  (gvMinusMeasure (S.image (fun x => g • x)) beta h).real (fmu_multiOpen T) = (gvMinusMeasure S beta h).real (fmu_multiOpen (T.image (fun x => g⁻¹ • x))) := by
-- proof
  apply StatMech.Ising.iptm_gvMinus_real_shift g S beta h T

/--
[iptm_minus_multiOpen_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_minus_multiOpen_monotone_eq
  {d : ℕ}
  {beta : ℝ}
  {h : ℝ}
  {T : Finset (Site d)}
  {n m : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hnm : n ≤ m) :
-- imply
  (minusMeasure d n beta h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T) ≤ (minusMeasure d m beta h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T) := by
-- proof
  apply StatMech.Ising.iptm_minus_multiOpen_monotone hbeta hh T hnm

/--
[iptm_minus_multiOpen_full_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_minus_multiOpen_full_tendsto_eq
  {d : ℕ}
  {beta : ℝ}
  {h : ℝ}
  {T : Finset (Site d)}
  {phi : ℕ → ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hphi : StrictMono phi)
  (hconv : WeakConvergesTo (fun n => minusMeasure d (phi n) beta h) (minusState d beta h)) :
-- imply
  Tendsto (fun m => (minusMeasure d m beta h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T)) atTop (nhds ((minusState d beta h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T))) := by
-- proof
  apply StatMech.Ising.iptm_minus_multiOpen_full_tendsto hbeta hh T hphi hconv

/--
[iptm_squeeze_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_squeeze_lower_eq
  {d : ℕ}
  {beta : ℝ}
  {h : ℝ}
  {g : Multiplicative (Site d)}
  {T : Finset (Site d)}
  {a m : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hcond : a + flc_vrad (Multiplicative.toAdd g) ≤ m) :
-- imply
  (minusMeasure d a beta h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T) ≤ (minusMeasure d m beta h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (T.image (fun x => g⁻¹ • x))) := by
-- proof
  apply StatMech.Ising.iptm_squeeze_lower hbeta hh g T hcond

/--
[iptm_squeeze_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_squeeze_upper_eq
  {d : ℕ}
  {beta : ℝ}
  {h : ℝ}
  {g : Multiplicative (Site d)}
  {T : Finset (Site d)}
  {m : ℕ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  (minusMeasure d m beta h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (T.image (fun x => g⁻¹ • x))) ≤ (minusMeasure d (m + flc_vrad (Multiplicative.toAdd g)) beta h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T) := by
-- proof
  apply StatMech.Ising.iptm_squeeze_upper hbeta hh g T m

/--
[iptm_minusMultiHomogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_minusMultiHomogeneous_eq
  {d : ℕ}
  {beta : ℝ}
  {h : ℝ}
  {g : Multiplicative (Site d)}
  {T : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  (minusState d beta h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T) = (minusState d beta h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (T.image (fun x => g⁻¹ • x))) := by
-- proof
  apply StatMech.Ising.iptm_minusMultiHomogeneous hbeta hh g T

/--
[iptm_minusState_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingMinusTIFromPlacement.lean)
-/
@[path]
private lemma iptm_minusState_isTranslationInvariant_eq
  {d : ℕ}
  {beta : ℝ}
  {h : ℝ}
-- given
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (minusState d beta h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.iptm_minusState_isTranslationInvariant hbeta hh


-- created on 2026-10-23
