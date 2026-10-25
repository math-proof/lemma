import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
open Filter MeasureTheory Topology StatMech StatMech.FrontierB


/--
[isClopen_currentCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentFiniteMarginals.lean)
-/
@[path]
private lemma isClopen_currentCylinder_eq
  {S : Finset E}
  {A : Set (↑S → ℕ)} :
-- imply
  IsClopen (currentCylinder S A) := by
-- proof
  apply StatMech.FrontierB.isClopen_currentCylinder S A

/--
[measurableSet_currentCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentFiniteMarginals.lean)
-/
@[path]
private lemma measurableSet_currentCylinder_eq
  [Countable E]
  {S : Finset E}
  {A : Set (↑S → ℕ)} :
-- imply
  MeasurableSet (currentCylinder S A) := by
-- proof
  apply StatMech.FrontierB.measurableSet_currentCylinder S A

/--
[currentMarginal_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentFiniteMarginals.lean)
-/
@[path]
private lemma currentMarginal_apply_eq
  [Countable E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {A : Set (↑S → ℕ)} :
-- imply
  (currentMarginal mu S : Measure (↑S → ℕ)) A = (mu : Measure (InfiniteCurrentConfig E)) (currentCylinder S A) := by
-- proof
  apply StatMech.FrontierB.currentMarginal_apply mu S A

/--
[WeakCurrentConverges.cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentFiniteMarginals.lean)
-/
@[path]
private lemma cylinder_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {A : Set (↑S → ℕ)}
-- given
  (h : WeakCurrentConverges mu nu) :
-- imply
  Tendsto (fun k => mu k (currentCylinder S A)) atTop (nhds (nu (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.cylinder h S A

/--
[WeakCurrentConverges.marginal_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentFiniteMarginals.lean)
-/
@[path]
private lemma marginal_apply_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {A : Set (↑S → ℕ)}
-- given
  (h : WeakCurrentConverges mu nu) :
-- imply
  Tendsto (fun k => currentMarginal (mu k) S A) atTop (nhds (currentMarginal nu S A)) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.marginal_apply h S A

/--
[restrictCurrent_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentFiniteMarginals.lean)
-/
@[path]
private lemma restrictCurrent_restrict_eq
  {S T : Finset E}
  {n : InfiniteCurrentConfig E}
-- given
  (hTS : T ⊆ S) :
-- imply
  Finset.restrict₂ (π := fun _ : E => ℕ) hTS (restrictCurrent S n) = restrictCurrent T n := by
-- proof
  apply StatMech.FrontierB.restrictCurrent_restrict hTS n

/--
[currentMarginal_map_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentFiniteMarginals.lean)
-/
@[path]
private lemma currentMarginal_map_restrict_eq
  [Countable E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S T : Finset E}
-- given
  (hTS : T ⊆ S) :
-- imply
  (currentMarginal mu S).map (Finset.measurable_restrict₂ (X := fun _ : E => ℕ) hTS).aemeasurable = currentMarginal mu T := by
-- proof
  apply StatMech.FrontierB.currentMarginal_map_restrict mu hTS

/--
[ProbabilityMeasure.ext_of_currentMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentFiniteMarginals.lean)
-/
@[path]
private lemma ext_of_currentMarginal_eq_eq
  [Countable E]
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (h : ∀ S : Finset E, currentMarginal mu S = currentMarginal nu S) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierB.ProbabilityMeasure.ext_of_currentMarginal_eq h

/--
[ProbabilityMeasure.ext_iff_currentMarginal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentFiniteMarginals.lean)
-/
@[path]
private lemma ext_iff_currentMarginal_eq_eq
  [Countable E]
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)} :
-- imply
  mu = nu ↔ ∀ S : Finset E, currentMarginal mu S = currentMarginal nu S := by
-- proof
  apply StatMech.FrontierB.ProbabilityMeasure.ext_iff_currentMarginal_eq


-- created on 2026-10-23
