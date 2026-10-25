import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.GenMixingCofinite
open MeasureTheory Set StatMech.ConfigSpace StatMech StatMech.FrontierB


/--
[isClopen_of_mem_measurableCylinders_bool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GenMixingCofinite.lean)
-/
@[path]
private lemma isClopen_of_mem_measurableCylinders_bool_eq
  [Countable E]
  [CommGroup G]
  [MulAction G E]
  {A : Set (ConfigSpace E)}
-- given
  (hA : A ∈ measurableCylinders (fun _ : E => Bool)) :
-- imply
  IsClopen A := by
-- proof
  apply StatMech.FrontierB.isClopen_of_mem_measurableCylinders_bool hA

/--
[isClopen_mem_measurableCylinders_bool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GenMixingCofinite.lean)
-/
@[path]
private lemma isClopen_mem_measurableCylinders_bool_eq
  [Countable E]
  [CommGroup G]
  [MulAction G E]
  {A : Set (ConfigSpace E)}
-- given
  (hA : IsClopen A) :
-- imply
  A ∈ measurableCylinders (fun _ : E => Bool) := by
-- proof
  apply StatMech.FrontierB.isClopen_mem_measurableCylinders_bool A hA

/--
[fmu_genMixing_exists_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GenMixingCofinite.lean)
-/
@[path]
private lemma fmu_genMixing_exists_not_mem_eq
  [Countable E]
  [CommGroup G]
  [MulAction G E]
  [Infinite G]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {family : Finset (Set (ConfigSpace E))}
  {K : Finset G}
  {delta : Real}
-- given
  (hti : IsTranslationInvariant (G := G) mu)
  (hmix : fmu_GenMixing (G := G) mu)
  (hfamily : ∀ A ∈ family, A ∈ measurableCylinders (fun _ : E => Bool))
  (hdelta : 0 < delta) :
-- imply
  ∃ g : G, g ∉ K ∧ ∀ A ∈ family, ∀ B ∈ family, abs (mu.real (A ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' B) - mu.real A * mu.real B) < delta := by
-- proof
  apply StatMech.FrontierB.fmu_genMixing_exists_not_mem hti hmix family hfamily K delta hdelta

/--
[fmu_genMixing_event_exists_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GenMixingCofinite.lean)
-/
@[path]
private lemma fmu_genMixing_event_exists_not_mem_eq
  [Countable E]
  [CommGroup G]
  [MulAction G E]
  [Infinite G]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {s : Set (ConfigSpace E)}
  {K : Finset G}
  {epsilon : Real}
-- given
  (hti : IsTranslationInvariant (G := G) mu)
  (hmix : fmu_GenMixing (G := G) mu)
  (hs : MeasurableSet s)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ g : G, g ∉ K ∧ abs (mu.real (s ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s) - (mu.real s) ^ 2) < 5 * epsilon := by
-- proof
  apply StatMech.FrontierB.fmu_genMixing_event_exists_not_mem hti hmix s hs K epsilon hepsilon


-- created on 2026-10-23
