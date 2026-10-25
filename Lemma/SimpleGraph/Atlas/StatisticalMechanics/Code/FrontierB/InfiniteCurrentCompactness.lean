import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
open Filter MeasureTheory Topology TopologicalSpace Set StatMech StatMech.FrontierB


/--
[isCompact_currentCoordinateBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentCompactness.lean)
-/
@[path]
private lemma isCompact_currentCoordinateBox_eq
  [Countable E]
  {K : E → ℕ} :
-- imply
  IsCompact (currentCoordinateBox K) := by
-- proof
  apply StatMech.FrontierB.isCompact_currentCoordinateBox K

/--
[currentCoordinateBox_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentCompactness.lean)
-/
@[path]
private lemma currentCoordinateBox_compl_eq
  [Countable E]
  {K : E → ℕ} :
-- imply
  (currentCoordinateBox K)ᶜ = ⋃ e : E, {n | K e ≤ n e} := by
-- proof
  apply StatMech.FrontierB.currentCoordinateBox_compl K

/--
[isTightMeasureSet_range_of_currentCoordinateBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentCompactness.lean)
-/
@[path]
private lemma isTightMeasureSet_range_of_currentCoordinateBox_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (hbox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : E → ℕ, ∀ i, ∑' e : E, (mu i : Measure _) {n : InfiniteCurrentConfig E | K e ≤ n e} ≤ ε) :
-- imply
  IsTightMeasureSet (Set.range fun i => (mu i : Measure (InfiniteCurrentConfig E))) := by
-- proof
  apply StatMech.FrontierB.isTightMeasureSet_range_of_currentCoordinateBox mu hbox

/--
[isTightMeasureSet_range_of_coordinate_tight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentCompactness.lean)
-/
@[path]
private lemma isTightMeasureSet_range_of_coordinate_tight_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (hcoord : ∀ e : E, ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ i, (mu i : Measure _) {n : InfiniteCurrentConfig E | K ≤ n e} ≤ ε) :
-- imply
  IsTightMeasureSet (Set.range fun i => (mu i : Measure (InfiniteCurrentConfig E))) := by
-- proof
  apply StatMech.FrontierB.isTightMeasureSet_range_of_coordinate_tight mu hcoord

/--
[isTightMeasureSet_range_of_uniform_inverse_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentCompactness.lean)
-/
@[path]
private lemma isTightMeasureSet_range_of_uniform_inverse_tail_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (B : ℝ≥0∞)
  (hB : B ≠ ∞)
  (htail : ∀ i e (K : ℕ), 0 < K → (mu i : Measure _) {n : InfiniteCurrentConfig E | K ≤ n e} ≤ B / K) :
-- imply
  IsTightMeasureSet (Set.range fun i => (mu i : Measure (InfiniteCurrentConfig E))) := by
-- proof
  apply StatMech.FrontierB.isTightMeasureSet_range_of_uniform_inverse_tail mu B hB htail

/--
[weakCurrent_subsequence_of_tight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentCompactness.lean)
-/
@[path]
private lemma weakCurrent_subsequence_of_tight_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (htight : IsTightMeasureSet (Set.range fun i => (mu i : Measure (InfiniteCurrentConfig E)))) :
-- imply
  ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig E)) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges (mu ∘ phi) nu := by
-- proof
  apply StatMech.FrontierB.weakCurrent_subsequence_of_tight mu htight

/--
[weakCurrent_subsequence_of_uniform_inverse_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentCompactness.lean)
-/
@[path]
private lemma weakCurrent_subsequence_of_uniform_inverse_tail_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (B : ℝ≥0∞)
  (hB : B ≠ ∞)
  (htail : ∀ i e (K : ℕ), 0 < K → (mu i : Measure _) {n : InfiniteCurrentConfig E | K ≤ n e} ≤ B / K) :
-- imply
  ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig E)) (phi : ℕ → ℕ), StrictMono phi ∧ WeakCurrentConverges (mu ∘ phi) nu := by
-- proof
  apply StatMech.FrontierB.weakCurrent_subsequence_of_uniform_inverse_tail mu B hB htail


-- created on 2026-10-23
