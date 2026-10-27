import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidencePIMSPhaseAssembly
open Filter MeasureTheory Topology StatMech StatMech.FrontierD


/--
[fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_evenTwoByOneCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_evenTwoByOneCrossingFloor_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale)) :
-- imply
  0 < fkQgt4CriticalFreeExactDiagonalRateLimit hq := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeExactDiagonalRateLimit_pos_of_evenTwoByOneCrossingFloor hq hhard hcross

/--
[fkQgt4CriticalFree_percolation_zero_of_evenTwoByOneCrossingFloor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_percolation_zero_of_evenTwoByOneCrossingFloor_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale)) :
-- imply
  let mu := (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : Measure (ConfigSpace (Sym2 (Site 2)))) mu.real (percolationEvent 2) = 0 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_percolation_zero_of_evenTwoByOneCrossingFloor hq hhard hcross

/--
[fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_boundaryIncidencePIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_boundaryIncidencePIMS_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hscheduled : FKQgt4BoundaryIncidenceScheduledFourCopy q (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_evenTwoByOneCrossingFloor_and_boundaryIncidencePIMS hq hhard hcross hscheduled

/--
[fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_boundaryIncidencePIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidencePIMSPhaseAssembly.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_boundaryIncidencePIMS_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hscheduled : FKQgt4BoundaryIncidenceScheduledFourCopy q (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2)) :
-- imply
  let hp := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 let hp1 := (selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 let hq0 : (0 : Real) < q := by linarith FK.IsFirstOrderTransition 2 hp hp1 hq0 ∧ FK.freeInfiniteVolume 2 hp hp1 hq0 ≠ FK.wiredInfiniteVolume 2 hp hp1 hq0 ∧ ((FK.wiredInfiniteVolume 2 hp hp1 hq0 : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (hasInfiniteClusterEvent 2) = 1 ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_evenTwoByOneCrossingFloor_and_boundaryIncidencePIMS hq hhard hcross hscheduled


-- created on 2026-10-23
