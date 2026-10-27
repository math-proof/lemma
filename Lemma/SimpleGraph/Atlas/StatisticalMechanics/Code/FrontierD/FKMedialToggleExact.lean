import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleExact
open SimpleGraph Equiv StatMech StatMech.FrontierD


/--
[fkMedialBlackDarts_reachable_iff_west_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleExact.lean)
-/
@[path]
private lemma fkMedialBlackDarts_reachable_iff_west_east_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  (fkMedialLoopGraph T pairing).Reachable (fkMedialBlackDart0 v).1 (fkMedialBlackDart1 v).1 <-> (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v) := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDarts_reachable_iff_west_east pairing v

/--
[fkMedialLoopCount_toggle_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleExact.lean)
-/
@[path]
private lemma fkMedialLoopCount_toggle_of_reachable_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
-- given
  (hconn : (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v)) :
-- imply
  fkMedialLoopCount T pairing + 1 = fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCount_toggle_of_reachable T pairing v hconn


-- created on 2026-10-23
