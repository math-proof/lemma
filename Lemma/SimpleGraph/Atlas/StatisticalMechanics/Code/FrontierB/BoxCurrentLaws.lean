import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.BoxCurrentLaws.Part3
open MeasureTheory StatMech StatMech.FrontierB


/--
[boxCurrentEdgeIncl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentLaws.lean)
-/
@[path]
private lemma boxCurrentEdgeIncl_injective_eq
  {d n : ℕ} :
-- imply
  Function.Injective (boxCurrentEdgeIncl d n) := by
-- proof
  apply StatMech.FrontierB.boxCurrentEdgeIncl_injective d n

/--
[extendBoxCurrent_included](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentLaws.lean)
-/
@[path]
private lemma extendBoxCurrent_included_eq
  {d n : ℕ}
  {m : EdgeCurrent (StatMech.FK.boxGraph d n)}
  {e : (StatMech.FK.boxGraph d n).edgeFinset} :
-- imply
  extendBoxCurrent d n m (boxCurrentEdgeIncl d n e) = m e := by
-- proof
  apply StatMech.FrontierB.extendBoxCurrent_included d n m e

/--
[extendBoxCurrent_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentLaws.lean)
-/
@[path]
private lemma extendBoxCurrent_outside_eq
  {d n : ℕ}
  {m : EdgeCurrent (StatMech.FK.boxGraph d n)}
  {e : Sym2 (Site d)}
-- given
  (he : e ∉ Set.range (boxCurrentEdgeIncl d n)) :
-- imply
  extendBoxCurrent d n m e = 0 := by
-- proof
  apply StatMech.FrontierB.extendBoxCurrent_outside d n m e he

/--
[measurable_extendBoxCurrent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentLaws.lean)
-/
@[path]
private lemma measurable_extendBoxCurrent_eq
  {d n : ℕ} :
-- imply
  Measurable (extendBoxCurrent d n) := by
-- proof
  apply StatMech.FrontierB.measurable_extendBoxCurrent d n

/--
[freeBoxCurrentMeasure_edge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentLaws.lean)
-/
@[path]
private lemma freeBoxCurrentMeasure_edge_tail_eq
  {d n : ℕ}
  {beta : ℝ}
  {e : (StatMech.FK.boxGraph d n).edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  (freeBoxCurrentMeasure d n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m (boxCurrentEdgeIncl d n e)} = (sourcelessCurrentMeasure (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta (fun _ => by positivity) : Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m e} := by
-- proof
  apply StatMech.FrontierB.freeBoxCurrentMeasure_edge_tail d n beta hbeta e K

/--
[plusBoxCurrentMeasure_edge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/BoxCurrentLaws.lean)
-/
@[path]
private lemma plusBoxCurrentMeasure_edge_tail_eq
  {d n : ℕ}
  {beta : ℝ}
  {e : (StatMech.FK.boxGraph d n).edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  (plusBoxCurrentMeasure d n beta hbeta : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m (boxCurrentEdgeIncl d n e)} = (boundaryCurrentMeasure (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta (fun _ => by positivity) (boxCurrentInterior d n) : Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m e} := by
-- proof
  apply StatMech.FrontierB.plusBoxCurrentMeasure_edge_tail d n beta hbeta e K


-- created on 2026-10-23
