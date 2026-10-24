import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology
open Filter MeasureTheory Topology StatMech StatMech.FrontierB


/--
[continuous_restrictCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma continuous_restrictCurrent_eq
  {S : Finset E} :
-- imply
  Continuous (restrictCurrent S : InfiniteCurrentConfig E → (↑S → ℕ)) := by
-- proof
  apply StatMech.FrontierB.continuous_restrictCurrent S

/--
[WeakCurrentConverges.marginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma marginal_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
-- given
  (h : WeakCurrentConverges mu nu) :
-- imply
  Tendsto (fun k => currentMarginal (mu k) S) atTop (nhds (currentMarginal nu S)) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.marginal h S

/--
[currentTrace_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma currentTrace_apply_eq
  {n : InfiniteCurrentConfig E}
  {e : E} :
-- imply
  currentTrace n e = true ↔ 0 < n e := by
-- proof
  apply StatMech.FrontierB.currentTrace_apply n e

/--
[continuous_currentTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma continuous_currentTrace_eq :
-- imply
  Continuous (currentTrace : InfiniteCurrentConfig E → ConfigSpace E) := by
-- proof
  apply StatMech.FrontierB.continuous_currentTrace

/--
[WeakCurrentConverges.trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma trace_eq
  [Countable E]
  {mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {nu : ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (h : WeakCurrentConverges mu nu) :
-- imply
  Tendsto (fun k => currentTraceLaw (mu k)) atTop (nhds (currentTraceLaw nu)) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.trace h

/--
[superposedCurrentTrace_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma superposedCurrentTrace_apply_eq
  {n : InfiniteCurrentConfig E × InfiniteCurrentConfig E}
  {e : E} :
-- imply
  superposedCurrentTrace n e = true ↔ 0 < n.1 e + n.2 e := by
-- proof
  apply StatMech.FrontierB.superposedCurrentTrace_apply n e

/--
[continuous_superposedCurrentTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma continuous_superposedCurrentTrace_eq :
-- imply
  Continuous (superposedCurrentTrace : InfiniteCurrentConfig E × InfiniteCurrentConfig E → ConfigSpace E) := by
-- proof
  apply StatMech.FrontierB.continuous_superposedCurrentTrace

/--
[independentSuperposedTraceLaw_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma independentSuperposedTraceLaw_comm_eq
  [Countable E]
  {mu nu : ProbabilityMeasure (InfiniteCurrentConfig E)} :
-- imply
  independentSuperposedTraceLaw mu nu = independentSuperposedTraceLaw nu mu := by
-- proof
  apply StatMech.FrontierB.independentSuperposedTraceLaw_comm mu nu

/--
[independentSuperposedTraceLaw_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma independentSuperposedTraceLaw_tendsto_eq
  [Countable E]
  {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (hmu : WeakCurrentConverges mu muLim)
  (hnu : WeakCurrentConverges nu nuLim) :
-- imply
  Tendsto (fun k => independentSuperposedTraceLaw (mu k) (nu k)) atTop (nhds (independentSuperposedTraceLaw muLim nuLim)) := by
-- proof
  apply StatMech.FrontierB.independentSuperposedTraceLaw_tendsto hmu hnu

/--
[measurable_currentShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma measurable_currentShift_eq
  [Group H]
  [MulAction H E]
  {g : H} :
-- imply
  Measurable (currentShift g : InfiniteCurrentConfig E → InfiniteCurrentConfig E) := by
-- proof
  apply StatMech.FrontierB.measurable_currentShift g

/--
[continuous_currentShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma continuous_currentShift_eq
  [Group H]
  [MulAction H E]
  {g : H} :
-- imply
  Continuous (currentShift g : InfiniteCurrentConfig E → InfiniteCurrentConfig E) := by
-- proof
  apply StatMech.FrontierB.continuous_currentShift g

/--
[currentTrace_semiconj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma currentTrace_semiconj_eq
  [Group H]
  [MulAction H E]
  {g : H} :
-- imply
  Function.Semiconj (currentTrace : InfiniteCurrentConfig E → ConfigSpace E) (currentShift g) (ConfigSpace.shift g) := by
-- proof
  apply StatMech.FrontierB.currentTrace_semiconj g

/--
[currentTrace_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma currentTrace_measurePreserving_eq
  [Countable E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)} :
-- imply
  MeasurePreserving currentTrace (mu : Measure (InfiniteCurrentConfig E)) (currentTraceLaw mu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.currentTrace_measurePreserving mu

/--
[CurrentIsTranslationInvariant.trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma trace_eq_2
  [Countable E]
  [Group H]
  [MulAction H E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (h : CurrentIsTranslationInvariant (H := H) (mu : Measure (InfiniteCurrentConfig E))) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := H) (currentTraceLaw mu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.CurrentIsTranslationInvariant.trace mu h

/--
[CurrentIsErgodic.trace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean)
-/
@[path]
private lemma trace_eq_3
  [Countable E]
  [Group H]
  [MulAction H E]
  {mu : ProbabilityMeasure (InfiniteCurrentConfig E)}
-- given
  (h : CurrentIsErgodic (H := H) (mu : Measure (InfiniteCurrentConfig E))) :
-- imply
  ConfigSpace.IsErgodic (G := H) (currentTraceLaw mu : Measure (ConfigSpace E)) := by
-- proof
  apply StatMech.FrontierB.CurrentIsErgodic.trace mu h


-- created on 2026-10-23
