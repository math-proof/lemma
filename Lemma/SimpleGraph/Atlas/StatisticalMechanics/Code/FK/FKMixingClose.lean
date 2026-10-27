import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKMixingClose
open MeasureTheory Filter Topology Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fmc_exists_cylinder_symmDiff_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean)
-/
@[path]
private lemma fmc_exists_cylinder_symmDiff_lt_eq
  [Group G]
  [MulAction G E]
  [Countable E]
  {μ : Measure (ConfigSpace E)}
  [IsFiniteMeasure μ]
  {A : Set (ConfigSpace E)}
  {ε : ℝ≥0∞}
-- given
  (hA : MeasurableSet A)
  (hε : 0 < ε) :
-- imply
  ∃ C ∈ measurableCylinders (fun _ : E => Bool), μ (C ∆ A) < ε := by
-- proof
  apply StatMech.FK.fmc_exists_cylinder_symmDiff_lt μ hA hε

/--
[fmc_invariant_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean)
-/
@[path]
private lemma fmc_invariant_sq_eq
  [Group G]
  [MulAction G E]
  [Countable E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {s : Set (ConfigSpace E)}
-- given
  (hμ : IsTranslationInvariant (G := G) μ)
  (hmix : fmc_SelfMixing (G := G) μ)
  (hs : MeasurableSet s)
  (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
-- imply
  μ.real s = (μ.real s) ^ 2 := by
-- proof
  apply StatMech.FK.fmc_invariant_sq hμ hmix hs hinv

/--
[fmc_real_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean)
-/
@[path]
private lemma fmc_real_zero_or_one_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {s : Set (ConfigSpace E)}
-- given
  (hsq : μ.real s = (μ.real s) ^ 2) :
-- imply
  μ s = 0 ∨ μ s = μ Set.univ := by
-- proof
  apply StatMech.FK.fmc_real_zero_or_one hsq

/--
[fmc_isErgodic_of_selfMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean)
-/
@[path]
private lemma fmc_isErgodic_of_selfMixing_eq
  [Group G]
  [MulAction G E]
  [Countable E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
-- given
  (hμ : IsTranslationInvariant (G := G) μ)
  (hmix : fmc_SelfMixing (G := G) μ) :
-- imply
  IsErgodic (G := G) μ := by
-- proof
  apply StatMech.FK.fmc_isErgodic_of_selfMixing hμ hmix

/--
[fmc_shift_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean)
-/
@[path]
private lemma fmc_shift_isIncreasing_eq
  [Group G]
  [MulAction G E]
  {A : Set (ConfigSpace E)}
  {g : G}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A) := by
-- proof
  apply StatMech.FK.fmc_shift_isIncreasing hA g

/--
[fmc_real_preimage_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean)
-/
@[path]
private lemma fmc_real_preimage_shift_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  {g : G}
  {A : Set (ConfigSpace E)}
-- given
  (hμ : IsTranslationInvariant (G := G) μ)
  (hA : MeasurableSet A) :
-- imply
  μ.real ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A) = μ.real A := by
-- proof
  apply StatMech.FK.fmc_real_preimage_shift hμ g hA

/--
[fmc_fkg_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean)
-/
@[path]
private lemma fmc_fkg_lower_bound_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  {A : Set (ConfigSpace E)}
  {g : G}
-- given
  (hμ : IsTranslationInvariant (G := G) μ)
  (hPA : ∀ {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B → MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
  (hA : IsIncreasing A)
  (hAmeas : MeasurableSet A) :
-- imply
  (μ.real A) ^ 2 ≤ μ.real (A ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' A) := by
-- proof
  apply StatMech.FK.fmc_fkg_lower_bound hμ hPA hA hAmeas g

/--
[fmc_wiredIV_isErgodic_of_mixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean)
-/
@[path]
private lemma fmc_wiredIV_isErgodic_of_mixing_eq
  [Group G]
  [MulAction G E]
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hmix : fmc_SelfMixing (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fmc_wiredIV_isErgodic_of_mixing hp hp1 hmix

/--
[fmc_freeIV_isErgodic_of_mixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingClose.lean)
-/
@[path]
private lemma fmc_freeIV_isErgodic_of_mixing_eq
  [Group G]
  [MulAction G E]
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hmix : fmc_SelfMixing (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fmc_freeIV_isErgodic_of_mixing hp hp1 hmix


-- created on 2026-10-23
