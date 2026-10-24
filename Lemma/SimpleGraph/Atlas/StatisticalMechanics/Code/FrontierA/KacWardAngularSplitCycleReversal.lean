import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitCycleReversal
open StatMech StatMech.FrontierA


/--
[kwAngularSplitGraphLoop_rev_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitCycleReversal.lean)
-/
@[path]
private lemma kwAngularSplitGraphLoop_rev_valid_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : Nat}
  [NeZero n]
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hvalid : kwGraphLoopNonbacktracking (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) loop) :
-- imply
  kwGraphLoopNonbacktracking (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwGraphLoopRev loop) := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitGraphLoop_rev_valid embedding loop hvalid

/--
[kwAngularSplitSpinorLoop_rev_eq_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitCycleReversal.lean)
-/
@[path]
private lemma kwAngularSplitSpinorLoop_rev_eq_inv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : Nat}
  [NeZero n]
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hvalid : kwGraphLoopNonbacktracking (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) loop) :
-- imply
  kwLoopPhaseProduct (kwAngularSplitSpinorPhase embedding) (kwGraphLoopRev loop) = (kwLoopPhaseProduct (kwAngularSplitSpinorPhase embedding) loop)⁻¹ := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinorLoop_rev_eq_inv embedding loop hvalid

/--
[kwAngularSplitSpinorLoopScalar_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitCycleReversal.lean)
-/
@[path]
private lemma kwAngularSplitSpinorLoopScalar_loopRev_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : Nat}
  [NeZero n]
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hvalid : kwGraphLoopNonbacktracking (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) loop) :
-- imply
  kwGraphLoopScalar (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitSpinorPhase embedding) (kwGraphLoopRev loop) = kwGraphLoopScalar (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitSpinorPhase embedding) loop := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitSpinorLoopScalar_loopRev embedding loop hvalid

/--
[kwAngularSplitLoopScalar_loopRev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitCycleReversal.lean)
-/
@[path]
private lemma kwAngularSplitLoopScalar_loopRev_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : Nat}
  [NeZero n]
  {loop : Fin n → (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)).Dart}
-- given
  (hvalid : kwGraphLoopNonbacktracking (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) loop) :
-- imply
  kwGraphLoopScalar (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitPhase embedding) (kwGraphLoopRev loop) = kwGraphLoopScalar (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitPhase embedding) loop := by
-- proof
  apply StatMech.FrontierA.kwAngularSplitLoopScalar_loopRev embedding loop hvalid

/--
[kwAngularSplit_loopReversalInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitCycleReversal.lean)
-/
@[path]
private lemma kwAngularSplit_loopReversalInvariant_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G} :
-- imply
  KWGraphLoopReversalInvariant (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding)) (kwAngularSplitPhase embedding) := by
-- proof
  apply StatMech.FrontierA.kwAngularSplit_loopReversalInvariant embedding


-- created on 2026-10-23
