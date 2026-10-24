import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.InfiniteCurrentPairCylinders
open Filter MeasureTheory Topology StatMech StatMech.FrontierB


/--
[continuous_restrictCurrentPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentPairCylinders.lean)
-/
@[path]
private lemma continuous_restrictCurrentPair_eq
  [Countable E]
  {S : Finset E} :
-- imply
  Continuous (restrictCurrentPair S : InfiniteCurrentConfig E × InfiniteCurrentConfig E → (↑S → ℕ) × (↑S → ℕ)) := by
-- proof
  apply StatMech.FrontierB.continuous_restrictCurrentPair S

/--
[isClopen_currentPairCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentPairCylinders.lean)
-/
@[path]
private lemma isClopen_currentPairCylinder_eq
  [Countable E]
  {S : Finset E}
  {A : Set ((↑S → ℕ) × (↑S → ℕ))} :
-- imply
  IsClopen (currentPairCylinder S A) := by
-- proof
  apply StatMech.FrontierB.isClopen_currentPairCylinder S A

/--
[measurableSet_currentPairCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentPairCylinders.lean)
-/
@[path]
private lemma measurableSet_currentPairCylinder_eq
  [Countable E]
  {S : Finset E}
  {A : Set ((↑S → ℕ) × (↑S → ℕ))} :
-- imply
  MeasurableSet (currentPairCylinder S A) := by
-- proof
  apply StatMech.FrontierB.measurableSet_currentPairCylinder S A

/--
[WeakCurrentConverges.pairCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentPairCylinders.lean)
-/
@[path]
private lemma pairCylinder_eq
  [Countable E]
  {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {A : Set ((↑S → ℕ) × (↑S → ℕ))}
-- given
  (hmu : WeakCurrentConverges mu muLim)
  (hnu : WeakCurrentConverges nu nuLim) :
-- imply
  Tendsto (fun k => (mu k).prod (nu k) (currentPairCylinder S A)) atTop (nhds (muLim.prod nuLim (currentPairCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.pairCylinder hmu hnu S A

/--
[WeakCurrentConverges.superposedTrace_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentPairCylinders.lean)
-/
@[path]
private lemma superposedTrace_real_eq
  [Countable E]
  {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {Q : Set (ConfigSpace E)}
-- given
  (hmu : WeakCurrentConverges mu muLim)
  (hnu : WeakCurrentConverges nu nuLim)
  (hQ : IsClopen Q) :
-- imply
  Tendsto (fun k => ((mu k).prod (nu k) : Measure _).real (superposedCurrentTrace ⁻¹' Q)) atTop (nhds ((muLim.prod nuLim : Measure _).real (superposedCurrentTrace ⁻¹' Q))) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.superposedTrace_real hmu hnu Q hQ

/--
[pairCylinder_limit_identity_of_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentPairCylinders.lean)
-/
@[path]
private lemma pairCylinder_limit_identity_of_eventually_eq
  [Countable E]
  {mu₁ mu₂ nu₁ nu₂ : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {mu₁Lim mu₂Lim nu₁Lim nu₂Lim : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S T : Finset E}
  {A : Set ((↑S → ℕ) × (↑S → ℕ))}
  {B : Set ((↑T → ℕ) × (↑T → ℕ))}
-- given
  (hmu₁ : WeakCurrentConverges mu₁ mu₁Lim)
  (hmu₂ : WeakCurrentConverges mu₂ mu₂Lim)
  (hnu₁ : WeakCurrentConverges nu₁ nu₁Lim)
  (hnu₂ : WeakCurrentConverges nu₂ nu₂Lim)
  (hid : ∀ᶠ k in atTop, (mu₁ k).prod (mu₂ k) (currentPairCylinder S A) = (nu₁ k).prod (nu₂ k) (currentPairCylinder T B)) :
-- imply
  mu₁Lim.prod mu₂Lim (currentPairCylinder S A) = nu₁Lim.prod nu₂Lim (currentPairCylinder T B) := by
-- proof
  apply StatMech.FrontierB.pairCylinder_limit_identity_of_eventually hmu₁ hmu₂ hnu₁ hnu₂ S T A B hid


-- created on 2026-10-23
