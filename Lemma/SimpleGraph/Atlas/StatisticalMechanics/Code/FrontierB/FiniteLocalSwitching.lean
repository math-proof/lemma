import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.FiniteLocalSwitching
open StatMech StatMech.FrontierB


/--
[gatedSourcePairSum_switching_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteLocalSwitching.lean)
-/
@[path]
private lemma gatedSourcePairSum_switching_local_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : ℝ}
  {J : Sym2 V → ℝ}
  {A : Finset V}
  {u v : V}
  {S : Finset (Sym2 V)}
  [DecidablePred Q]
-- given
  (huv : u ≠ v)
  (Q : (↑S → ℕ) → Prop) :
-- imply
  gatedSourcePairSum G beta J (A ∆ ({u, v} : Finset V)) {u, v} (currentLocalPattern S Q) = gatedSourcePairSum G beta J A ∅ (fun m => currentLocalPattern S Q m ∧ CurrentConnected G m u v) := by
-- proof
  apply StatMech.FrontierB.gatedSourcePairSum_switching_local G beta J A huv S Q

/--
[isClopen_currentSuperpositionCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteLocalSwitching.lean)
-/
@[path]
private lemma isClopen_currentSuperpositionCylinder_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Countable E]
  {S : Finset E}
  {A : Set (↑S → ℕ)} :
-- imply
  IsClopen (currentSuperpositionCylinder S A) := by
-- proof
  apply StatMech.FrontierB.isClopen_currentSuperpositionCylinder G S A

/--
[WeakCurrentConverges.superpositionCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteLocalSwitching.lean)
-/
@[path]
private lemma superpositionCylinder_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Countable E]
  {mu nu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)}
  {muLim nuLim : ProbabilityMeasure (InfiniteCurrentConfig E)}
  {S : Finset E}
  {A : Set (↑S → ℕ)}
-- given
  (hmu : WeakCurrentConverges mu muLim)
  (hnu : WeakCurrentConverges nu nuLim) :
-- imply
  Filter.Tendsto (fun k => (mu k).prod (nu k) (currentSuperpositionCylinder S A)) Filter.atTop (nhds (muLim.prod nuLim (currentSuperpositionCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.WeakCurrentConverges.superpositionCylinder G hmu hnu S A


-- created on 2026-10-23
