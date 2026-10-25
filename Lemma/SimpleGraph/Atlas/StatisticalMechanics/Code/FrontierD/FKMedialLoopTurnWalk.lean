import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTurnWalk.Part2
open Equiv StatMech StatMech.FrontierD


/--
[two_mul_turnPow_strandDirection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurnWalk.lean)
-/
@[path]
private lemma two_mul_turnPow_strandDirection_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  2 * ons_turnPow (fkMedialStrandDirection pairing d.1) (fkMedialStrandDirection pairing (fkMedialBlackBoundaryPerm pairing d).1) = -(turnSign (pairing d.1.1) (fkMedialVertexParity d.1.1) + turnSign (pairing (fkMedialBlackBoundaryPerm pairing d).1.1) (fkMedialVertexParity (fkMedialBlackBoundaryPerm pairing d).1.1)) := by
-- proof
  apply StatMech.FrontierD.two_mul_turnPow_strandDirection pairing d

/--
[connectedComponentMk_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurnWalk.lean)
-/
@[path]
private lemma connectedComponentMk_localMate_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  (fkMedialLoopGraph T pairing).connectedComponentMk (fkMedialLocalMate pairing d) = (fkMedialLoopGraph T pairing).connectedComponentMk d := by
-- proof
  apply StatMech.FrontierD.connectedComponentMk_localMate pairing d

/--
[canonicalComponentTurn_eq_blackComponentTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurnWalk.lean)
-/
@[path]
private lemma canonicalComponentTurn_eq_blackComponentTurn_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {C : FKMedialLoop T pairing} :
-- imply
  canonicalComponentTurn pairing C = blackComponentTurn pairing C := by
-- proof
  apply StatMech.FrontierD.canonicalComponentTurn_eq_blackComponentTurn pairing C

/--
[fkMedialBlackBoundaryPerm_apply_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurnWalk.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_apply_ne_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  fkMedialBlackBoundaryPerm pairing d ≠ d := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_apply_ne pairing d

/--
[canonicalComponentTurn_eq_toList_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurnWalk.lean)
-/
@[path]
private lemma canonicalComponentTurn_eq_toList_sum_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {C : FKMedialLoop T pairing}
  {d : FKMedialBlackDart T}
-- given
  (hdC : (fkMedialLoopGraph T pairing).connectedComponentMk d.1 = C) :
-- imply
  canonicalComponentTurn pairing C = (((fkMedialBlackBoundaryPerm pairing).toList d).map (fun e : FKMedialBlackDart T => turnSign (pairing e.1.1) (fkMedialVertexParity e.1.1))).sum := by
-- proof
  apply StatMech.FrontierD.canonicalComponentTurn_eq_toList_sum pairing C d hdC

/--
[cyclicTurnSum_toList_strandDirections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLoopTurnWalk.lean)
-/
@[path]
private lemma cyclicTurnSum_toList_strandDirections_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  ons_cyclicTurnSum (((fkMedialBlackBoundaryPerm pairing).toList d).map (fun e : FKMedialBlackDart T => fkMedialStrandDirection pairing e.1)) = -(((fkMedialBlackBoundaryPerm pairing).toList d).map (fun e : FKMedialBlackDart T => turnSign (pairing e.1.1) (fkMedialVertexParity e.1.1)) |>.sum) := by
-- proof
  apply StatMech.FrontierD.cyclicTurnSum_toList_strandDirections pairing d


-- created on 2026-10-23
