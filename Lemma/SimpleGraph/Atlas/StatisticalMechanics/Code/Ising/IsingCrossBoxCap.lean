import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.IsingCrossBoxCap
open MeasureTheory Filter Topology Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.Ising


/--
[icb_plus_box_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean)
-/
@[path]
private lemma icb_plus_box_monotone_eq
  {d : ℕ}
  {N m : ℕ}
  {A : Set (ConfigSpace (Site d))}
-- given
  (hNm : N ≤ m)
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hA : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real A ≤ (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A := by
-- proof
  apply StatMech.Ising.icb_plus_box_monotone hNm β h hβ hh hA hAinc

/--
[icb_multiOpen_glue_ovrBox_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean)
-/
@[path]
private lemma icb_multiOpen_glue_ovrBox_eq_eq
  {d : ℕ}
  {N m : ℕ}
  {S : Finset (Site d)}
-- given
  (hNm : N ≤ m)
  (hS : ∀ x ∈ S, x ∉ box d N)
  (σ : {x // x ∈ box d m} → Bool)
  (τ : {x // x ∈ box d N} → Bool) :
-- imply
  (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) (ovrBox hNm σ τ)) = (fmu_multiOpen S).indicator (fun _ => (1:ℝ)) (glue (plusField d) σ) := by
-- proof
  apply StatMech.Ising.icb_multiOpen_glue_ovrBox_eq hNm S hS σ τ

/--
[icb_box_cross_cap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean)
-/
@[path]
private lemma icb_box_cross_cap_eq
  {d : ℕ}
  {N m : ℕ}
  {A : Set (ConfigSpace (Site d))}
  {S : Finset (Site d)}
-- given
  (hNm : N ≤ m)
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hA : MeasurableSet A)
  (hAinc : IsIncreasing A)
  (hS : ∀ x ∈ S, x ∉ box d N) :
-- imply
  (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (A ∩ fmu_multiOpen S) ≤ (plusMeasure d N β h : Measure (ConfigSpace (Site d))).real A * (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen S) := by
-- proof
  apply StatMech.Ising.icb_box_cross_cap hNm β h hβ hh hA hAinc S hS

/--
[icb_inv_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean)
-/
@[path]
private lemma icb_inv_smul_eq
  {d : ℕ}
  {i₀ : Fin d}
  {R : ℤ}
  {x : Site d} :
-- imply
  ((Multiplicative.ofAdd (- icb_shiftVec i₀ R))⁻¹ • x) = x + icb_shiftVec i₀ R := by
-- proof
  apply StatMech.Ising.icb_inv_smul i₀ R x

/--
[icb_shifted_notMem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean)
-/
@[path]
private lemma icb_shifted_notMem_box_eq
  {d : ℕ}
  {i₀ : Fin d}
  {N : ℕ}
  {R : ℤ}
  {x : Site d}
-- given
  (hR : (N : ℤ) + |x i₀| < R) :
-- imply
  ((Multiplicative.ofAdd (- icb_shiftVec i₀ R))⁻¹ • x) ∉ box d N := by
-- proof
  apply StatMech.Ising.icb_shifted_notMem_box i₀ hR

/--
[icb_exists_far_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean)
-/
@[path]
private lemma icb_exists_far_shift_eq
  {d : ℕ}
  {P : Finset (Finset (Site d))}
  {N : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∃ g : Multiplicative (Site d), ∀ T' ∈ P, ∀ x ∈ T', (g⁻¹ • x : Site d) ∉ box d N := by
-- proof
  apply StatMech.Ising.icb_exists_far_shift hd P N

/--
[icb_plusState_upperDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean)
-/
@[path]
private lemma icb_plusState_upperDecay_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  fmu_UpperDecay (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.icb_plusState_upperDecay hd hβ hh hti

/--
[icb_plusState_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean)
-/
@[path]
private lemma icb_plusState_isErgodic_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.icb_plusState_isErgodic hd hβ hh hti

/--
[icb_plusState_isInvariantExtremePoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingCrossBoxCap.lean)
-/
@[path]
private lemma icb_plusState_isInvariantExtremePoint_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
-- given
  (hd : 1 ≤ d)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.icb_plusState_isInvariantExtremePoint hd hβ hh hti


-- created on 2026-10-23
