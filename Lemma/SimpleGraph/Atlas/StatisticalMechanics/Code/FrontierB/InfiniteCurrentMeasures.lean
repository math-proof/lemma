import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
open Filter MeasureTheory StatMech StatMech.FrontierB


/--
[infiniteCurrentBoxSubsequence_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentMeasures.lean)
-/
@[path]
private lemma infiniteCurrentBoxSubsequence_strictMono_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  StrictMono (infiniteCurrentBoxSubsequence d beta hbeta) := by
-- proof
  apply StatMech.FrontierB.infiniteCurrentBoxSubsequence_strictMono d beta hbeta

/--
[freeBoxCurrentMeasure_tendsto_infiniteFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentMeasures.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_tendsto_infiniteFree_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  WeakCurrentConverges ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ infiniteCurrentBoxSubsequence d beta hbeta) (infiniteFreeCurrentMeasure d beta hbeta) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta

/--
[plusBoxCurrentMeasure_tendsto_infinitePlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentMeasures.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_tendsto_infinitePlus_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  WeakCurrentConverges ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ infiniteCurrentBoxSubsequence d beta hbeta) (infinitePlusCurrentMeasure d beta hbeta) := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta

/--
[freeBoxCurrentMeasure_cylinder_tendsto_infiniteFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentMeasures.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_cylinder_tendsto_infiniteFree_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {A : Set (↑S → ℕ)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Tendsto (fun k => freeBoxCurrentMeasure d (infiniteCurrentBoxSubsequence d beta hbeta k) beta hbeta (currentCylinder S A)) atTop (nhds (infiniteFreeCurrentMeasure d beta hbeta (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_cylinder_tendsto_infiniteFree d beta hbeta S A

/--
[plusBoxCurrentMeasure_cylinder_tendsto_infinitePlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentMeasures.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_cylinder_tendsto_infinitePlus_eq
  {d : ℕ}
  {beta : ℝ}
  {S : Finset (Sym2 (Site d))}
  {A : Set (↑S → ℕ)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Tendsto (fun k => plusBoxCurrentMeasure d (infiniteCurrentBoxSubsequence d beta hbeta k) beta hbeta (currentCylinder S A)) atTop (nhds (infinitePlusCurrentMeasure d beta hbeta (currentCylinder S A))) := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_cylinder_tendsto_infinitePlus d beta hbeta S A


-- created on 2026-10-23
