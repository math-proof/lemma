import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorCrosscut
open Set SimpleGraph StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_openWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCrosscut.lean)
-/
@[path]
private lemma finiteDeepOpenExitedJoinedBoundaryArmEvent_openWalk_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r R c d : Real}
  {width : Nat}
  {L U : Finset V}
-- given
  (hrR : r ≤ R)
  (h : omega ∈ E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ z : V, z ∉ E.rightHalfPlaneVertices r ∧ ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ w : V, w ∉ E.rightHalfPlaneVertices r ∧ ∃ q : (P.openSubgraph omega).Walk z w, b ∈ q.support ∧ u ∈ q.support ∧ ∀ v ∈ q.support, v = z ∨ v = w ∨ v ∈ E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_openWalk E hrR h

/--
[PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_simpleCrosscut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCrosscut.lean)
-/
@[path]
private lemma finiteDeepOpenExitedJoinedBoundaryArmEvent_simpleCrosscut_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {omega : ConfigSpace (Sym2 V)}
  {r R c d : Real}
  {width : Nat}
  {L U : Finset V}
-- given
  (hrR : r ≤ R)
  (hcd : c < d)
  (h : omega ∈ E.finiteDeepOpenExitedJoinedBoundaryArmEvent r R c d width L U) :
-- imply
  ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ q : P.graph.Walk b u, q.IsPath ∧ ¬q.Nil ∧ Function.Injective (E.simpleWalkArc q) ∧ (∀ {x y : V}, s(x, y) ∈ q.edges → omega s(x, y) = true) ∧ ∀ v ∈ q.support, v ∈ E.rightHalfPlaneVertices r := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent_simpleCrosscut E hrR hcd h


-- created on 2026-10-23
