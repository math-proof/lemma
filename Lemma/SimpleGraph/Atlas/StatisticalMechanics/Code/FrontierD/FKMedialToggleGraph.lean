import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleGraph
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkMedialLoopGraph_toggle_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleGraph.lean)
-/
@[path]
private lemma fkMedialLoopGraph_toggle_eq_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkMedialLoopGraph T (fkMedialTogglePairingAt pairing v) = (fkMedialLoopGraph T pairing).deleteEdges (fkMedialOldLocalEdges pairing v) ⊔ fromEdgeSet (fkMedialNewLocalEdges pairing v) := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopGraph_toggle_eq T pairing v


-- created on 2026-10-23
