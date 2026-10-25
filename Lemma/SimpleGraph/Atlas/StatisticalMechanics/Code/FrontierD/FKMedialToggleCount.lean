import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleCount
open SimpleGraph Set StatMech StatMech.FrontierD


/--
[fkMedialNewLocalEdges_eq_crossed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleCount.lean)
-/
@[path]
private lemma fkMedialNewLocalEdges_eq_crossed_eq
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkMedialNewLocalEdges pairing v = {s(fkMedialWestDart v, fkMedialLocalMate pairing (fkMedialEastDart v)), s(fkMedialEastDart v, fkMedialLocalMate pairing (fkMedialWestDart v))} := by
-- proof
  apply StatMech.FrontierD.fkMedialNewLocalEdges_eq_crossed pairing v

/--
[fkMedialLoopCount_toggle_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleCount.lean)
-/
@[path]
private lemma fkMedialLoopCount_toggle_of_not_reachable_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
-- given
  (hdisc : ¬ (fkMedialLoopGraph T pairing).Reachable (fkMedialWestDart v) (fkMedialEastDart v)) :
-- imply
  fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) + 1 = fkMedialLoopCount T pairing := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCount_toggle_of_not_reachable T pairing v hdisc

/--
[fkMedialLoopCount_toggle_le_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialToggleCount.lean)
-/
@[path]
private lemma fkMedialLoopCount_toggle_le_add_one_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) ≤ fkMedialLoopCount T pairing + 1 := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCount_toggle_le_add_one T pairing v


-- created on 2026-10-23
