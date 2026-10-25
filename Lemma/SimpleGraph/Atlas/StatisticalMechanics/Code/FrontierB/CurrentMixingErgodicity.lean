import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentMixingErgodicity.Part2
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[current_exists_cylinder_symmDiff_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean)
-/
@[path]
private lemma current_exists_cylinder_symmDiff_lt_eq
  [Group H]
  [MulAction H E]
  [Countable E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsFiniteMeasure mu]
  {A : Set (InfiniteCurrentConfig E)}
  {epsilon : ENNReal}
-- given
  (hA : MeasurableSet A)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ C ∈ measurableCylinders (fun _ : E => Nat), mu (C ∆ A) < epsilon := by
-- proof
  apply StatMech.FrontierB.current_exists_cylinder_symmDiff_lt mu hA hepsilon

/--
[current_invariant_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean)
-/
@[path]
private lemma current_invariant_sq_eq
  [Group H]
  [MulAction H E]
  [Countable E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsProbabilityMeasure mu]
  {s : Set (InfiniteCurrentConfig E)}
-- given
  (hmu : CurrentIsTranslationInvariant (H := H) mu)
  (hmix : CurrentSelfMixing (H := H) mu)
  (hs : MeasurableSet s)
  (hinv : ∀ g : H, (currentShift g) ⁻¹' s = s) :
-- imply
  mu.real s = (mu.real s) ^ 2 := by
-- proof
  apply StatMech.FrontierB.current_invariant_sq hmu hmix hs hinv

/--
[current_real_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean)
-/
@[path]
private lemma current_real_zero_or_one_eq
  [Group H]
  [MulAction H E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsProbabilityMeasure mu]
  {s : Set (InfiniteCurrentConfig E)}
-- given
  (hsq : mu.real s = (mu.real s) ^ 2) :
-- imply
  mu s = 0 ∨ mu s = mu Set.univ := by
-- proof
  apply StatMech.FrontierB.current_real_zero_or_one hsq

/--
[current_isErgodic_of_selfMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean)
-/
@[path]
private lemma current_isErgodic_of_selfMixing_eq
  [Group H]
  [MulAction H E]
  [Countable E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsProbabilityMeasure mu]
-- given
  (hmu : CurrentIsTranslationInvariant (H := H) mu)
  (hmix : CurrentSelfMixing (H := H) mu) :
-- imply
  CurrentIsErgodic (H := H) mu := by
-- proof
  apply StatMech.FrontierB.current_isErgodic_of_selfMixing hmu hmix

/--
[current_isTranslationInvariant_of_cylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean)
-/
@[path]
private lemma current_isTranslationInvariant_of_cylinders_eq
  [Group H]
  [MulAction H E]
  [Countable E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsProbabilityMeasure mu]
-- given
  (h : ∀ (g : H) (S : Finset E) (A : Set (↑S -> Nat)), mu ((currentShift g) ⁻¹' currentCylinder S A) = mu (currentCylinder S A)) :
-- imply
  CurrentIsTranslationInvariant (H := H) mu := by
-- proof
  apply StatMech.FrontierB.current_isTranslationInvariant_of_cylinders h

/--
[current_selfMixing_of_cylinderPairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean)
-/
@[path]
private lemma current_selfMixing_of_cylinderPairMixing_eq
  [Group H]
  [MulAction H E]
  [Countable E]
  {mu : Measure (InfiniteCurrentConfig E)}
-- given
  (hmix : CurrentCylinderPairMixing (H := H) mu) :
-- imply
  CurrentSelfMixing (H := H) mu := by
-- proof
  apply StatMech.FrontierB.current_selfMixing_of_cylinderPairMixing hmix

/--
[current_isErgodic_of_cylinderPairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentMixingErgodicity.lean)
-/
@[path]
private lemma current_isErgodic_of_cylinderPairMixing_eq
  [Group H]
  [MulAction H E]
  [Countable E]
  {mu : Measure (InfiniteCurrentConfig E)}
  [IsProbabilityMeasure mu]
-- given
  (hmu : CurrentIsTranslationInvariant (H := H) mu)
  (hmix : CurrentCylinderPairMixing (H := H) mu) :
-- imply
  CurrentIsErgodic (H := H) mu := by
-- proof
  apply StatMech.FrontierB.current_isErgodic_of_cylinderPairMixing hmu hmix


-- created on 2026-10-23
