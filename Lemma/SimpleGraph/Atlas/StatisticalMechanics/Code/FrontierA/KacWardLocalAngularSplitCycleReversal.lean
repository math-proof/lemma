import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitCycleReversal
open StatMech StatMech.FrontierA


/--
[kwLocalAngularSplitGraphLoop_rev_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitCycleReversal.lean)
-/
@[path]
private lemma kwLocalAngularSplitGraphLoop_rev_valid_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {n : Nat}
  [NeZero n]
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (data.order)).Dart}
-- given
  (hvalid : kwGraphLoopNonbacktracking (kwOrderedDartPortSplitGraph G (data.order)) loop) :
-- imply
  kwGraphLoopNonbacktracking (kwOrderedDartPortSplitGraph G (data.order)) (kwGraphLoopRev loop) := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitGraphLoop_rev_valid data loop hvalid

/--
[kwLocalAngularSplitSpinorLoop_rev_eq_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitCycleReversal.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinorLoop_rev_eq_inv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {n : Nat}
  [NeZero n]
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (data.order)).Dart}
-- given
  (hvalid : kwGraphLoopNonbacktracking (kwOrderedDartPortSplitGraph G (data.order)) loop) :
-- imply
  kwLoopPhaseProduct (kwLocalAngularSplitSpinorPhase data) (kwGraphLoopRev loop) = (kwLoopPhaseProduct (kwLocalAngularSplitSpinorPhase data) loop)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinorLoop_rev_eq_inv data loop hvalid

/--
[kwLocalAngularSplitSpinorLoopScalar_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitCycleReversal.lean)
-/
@[path]
private lemma kwLocalAngularSplitSpinorLoopScalar_loopRev_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {n : Nat}
  [NeZero n]
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (data.order)).Dart}
-- given
  (hvalid : kwGraphLoopNonbacktracking (kwOrderedDartPortSplitGraph G (data.order)) loop) :
-- imply
  kwGraphLoopScalar (kwOrderedDartPortSplitGraph G (data.order)) (kwLocalAngularSplitSpinorPhase data) (kwGraphLoopRev loop) = kwGraphLoopScalar (kwOrderedDartPortSplitGraph G (data.order)) (kwLocalAngularSplitSpinorPhase data) loop := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitSpinorLoopScalar_loopRev data loop hvalid

/--
[kwLocalAngularSplitLoopScalar_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitCycleReversal.lean)
-/
@[path]
private lemma kwLocalAngularSplitLoopScalar_loopRev_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G}
  {n : Nat}
  [NeZero n]
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (data.order)).Dart}
-- given
  (hvalid : kwGraphLoopNonbacktracking (kwOrderedDartPortSplitGraph G (data.order)) loop) :
-- imply
  kwGraphLoopScalar (kwOrderedDartPortSplitGraph G (data.order)) (kwLocalAngularSplitPhase data) (kwGraphLoopRev loop) = kwGraphLoopScalar (kwOrderedDartPortSplitGraph G (data.order)) (kwLocalAngularSplitPhase data) loop := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplitLoopScalar_loopRev data loop hvalid

/--
[kwLocalAngularSplit_loopReversalInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitCycleReversal.lean)
-/
@[path]
private lemma kwLocalAngularSplit_loopReversalInvariant_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {data : KWLocalAngularData G} :
-- imply
  KWGraphLoopReversalInvariant (kwOrderedDartPortSplitGraph G (data.order)) (kwLocalAngularSplitPhase data) := by
-- proof
  apply StatMech.FrontierA.kwLocalAngularSplit_loopReversalInvariant data


-- created on 2026-10-23
