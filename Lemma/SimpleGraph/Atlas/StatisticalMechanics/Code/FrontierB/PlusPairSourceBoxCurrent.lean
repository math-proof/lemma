import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.PlusPairSourceBoxCurrent.Part2
open MeasureTheory StatMech StatMech.FrontierB


/--
[boxSiteSucc_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceBoxCurrent.lean)
-/
@[path]
private lemma boxSiteSucc_interior_eq
  {d n : ℕ}
  {x : StatMech.FK.boxVerts d n} :
-- imply
  boxSiteSucc x ∈ boxCurrentInterior d (n + 1) := by
-- proof
  apply StatMech.FrontierB.boxSiteSucc_interior x

/--
[boxSiteSucc_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceBoxCurrent.lean)
-/
@[path]
private lemma boxSiteSucc_ne_eq
  {d n : ℕ}
  {x y : StatMech.FK.boxVerts d n}
-- given
  (hxy : x ≠ y) :
-- imply
  boxSiteSucc x ≠ boxSiteSucc y := by
-- proof
  apply StatMech.FrontierB.boxSiteSucc_ne hxy

/--
[pair_boxSiteSucc_inter_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceBoxCurrent.lean)
-/
@[path]
private lemma pair_boxSiteSucc_inter_interior_eq
  {d n : ℕ}
  {x y : StatMech.FK.boxVerts d n} :
-- imply
  ({boxSiteSucc x, boxSiteSucc y} : Finset (StatMech.FK.boxVerts d (n + 1))) ∩ boxCurrentInterior d (n + 1) = {boxSiteSucc x, boxSiteSucc y} := by
-- proof
  apply StatMech.FrontierB.pair_boxSiteSucc_inter_interior x y

/--
[plusPairBoundarySourceCurrentSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceBoxCurrent.lean)
-/
@[path]
private lemma plusPairBoundarySourceCurrentSum_pos_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y) :
-- imply
  0 < boundarySourceCurrentSum (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y} := by
-- proof
  apply StatMech.FrontierB.plusPairBoundarySourceCurrentSum_pos d n beta hbeta x y hxy

/--
[plusPairSourceBoxCurrentMeasure_edge_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusPairSourceBoxCurrent.lean)
-/
@[path]
private lemma plusPairSourceBoxCurrentMeasure_edge_tail_eq
  {d n : ℕ}
  {beta : ℝ}
  {x y : StatMech.FK.boxVerts d n}
  {e : (StatMech.FK.boxGraph d (n + 1)).edgeFinset}
  {K : ℕ}
-- given
  (hbeta : 0 < beta)
  (hxy : x ≠ y) :
-- imply
  (plusPairSourceBoxCurrentMeasure d n beta hbeta x y hxy : Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m (boxCurrentEdgeIncl d (n + 1) e)} = (boundarySourceCurrentPMF (StatMech.FK.boxGraph d (n + 1)) beta (fun _ => 1) hbeta.le (fun _ => by positivity) (boxCurrentInterior d (n + 1)) {boxSiteSucc x, boxSiteSucc y} (plusPairBoundarySourceCurrentSum_pos d n beta hbeta x y hxy)).toMeasure {m | K ≤ m e} := by
-- proof
  apply StatMech.FrontierB.plusPairSourceBoxCurrentMeasure_edge_tail d n beta hbeta x y hxy e K


-- created on 2026-10-23
