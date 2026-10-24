import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.IsingPlusErgodicClose
open MeasureTheory Filter Topology Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.Ising


/--
[ipe_multiOpen_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_multiOpen_isClopen_eq
  {d : ℕ}
  {T : Finset (Site d)} :
-- imply
  IsClopen (fmu_multiOpen (E := Site d) T) := by
-- proof
  apply StatMech.Ising.ipe_multiOpen_isClopen T

/--
[ipe_cross_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_cross_isClopen_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {T T' : Finset (Site d)} :
-- imply
  IsClopen (fmu_multiOpen T ∩ (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' fmu_multiOpen T') := by
-- proof
  apply StatMech.Ising.ipe_cross_isClopen g T T'

/--
[ipe_glue_preimage_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_glue_preimage_increasing_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {T : Finset (Site d)} :
-- imply
  IsIncreasing ((fun τ : {x // x ∈ box d n} → Bool => glue η τ) ⁻¹' fmu_multiOpen T) := by
-- proof
  apply StatMech.Ising.ipe_glue_preimage_increasing η n T

/--
[ipe_fvMeasure_fkg_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_fvMeasure_fkg_multiOpen_eq
  {d : ℕ}
  {η : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
  {T₁ T₂ : Finset (Site d)}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ) :
-- imply
  (fvMeasure η n B β h).real (fmu_multiOpen T₁) * (fvMeasure η n B β h).real (fmu_multiOpen T₂) ≤ (fvMeasure η n B β h).real (fmu_multiOpen T₁ ∩ fmu_multiOpen T₂) := by
-- proof
  apply StatMech.Ising.ipe_fvMeasure_fkg_multiOpen η n B hβ h T₁ T₂

/--
[ipe_plusMeasure_fkg_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_plusMeasure_fkg_multiOpen_eq
  {d : ℕ}
  {n : ℕ}
  {β : ℝ}
  {T₁ T₂ : Finset (Site d)}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ) :
-- imply
  (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₁) * (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₂) ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₁ ∩ fmu_multiOpen T₂) := by
-- proof
  apply StatMech.Ising.ipe_plusMeasure_fkg_multiOpen n hβ h T₁ T₂

/--
[ipe_plusState_fkg_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_plusState_fkg_multiOpen_eq
  {d : ℕ}
  {β : ℝ}
  {T₁ T₂ : Finset (Site d)}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ) :
-- imply
  (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₁) * (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₂) ≤ (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T₁ ∩ fmu_multiOpen T₂) := by
-- proof
  apply StatMech.Ising.ipe_plusState_fkg_multiOpen hβ h T₁ T₂

/--
[ipe_plusState_pairMixing_of_upperDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_plusState_pairMixing_of_upperDecay_eq
  {d : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))))
  (hup : fmu_UpperDecay (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  fmu_PairMixing (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.ipe_plusState_pairMixing_of_upperDecay hβ h hti hup

/--
[ipe_plusState_isErgodic_of_upperDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_plusState_isErgodic_of_upperDecay_eq
  {d : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))))
  (hup : fmu_UpperDecay (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.ipe_plusState_isErgodic_of_upperDecay hβ h hti hup

/--
[ipe_plusState_isInvariantExtremePoint_of_upperDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_plusState_isInvariantExtremePoint_of_upperDecay_eq
  {d : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))))
  (hup : fmu_UpperDecay (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.ipe_plusState_isInvariantExtremePoint_of_upperDecay hβ h hti hup

/--
[ipe_upperDecay_dirac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_upperDecay_dirac_eq
  {d : ℕ} :
-- imply
  fmu_UpperDecay (G := Multiplicative (Site d)) (Measure.dirac (fun _ : Site d => true)) := by
-- proof
  apply StatMech.Ising.ipe_upperDecay_dirac

/--
[ipe_fkg_lower_strict_excludes_fixedShift_decoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusErgodicClose.lean)
-/
@[path]
private lemma ipe_fkg_lower_strict_excludes_fixedShift_decoupling_eq
  {d : ℕ}
  {β : ℝ}
  {T T' : Finset (Site d)}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ) :
-- imply
  (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T) * (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T') ≤ (plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen T ∩ (shift (1 : Multiplicative (Site d)) : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' fmu_multiOpen T') := by
-- proof
  apply StatMech.Ising.ipe_fkg_lower_strict_excludes_fixedShift_decoupling hβ h T T'


-- created on 2026-10-23
