import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKMedialLayeredCutBalance
open StatMech StatMech.FrontierD


/--
[fkMedialLoopCount_twoLayer_twoToggle_eq_of_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLayeredCutBalance.lean)
-/
@[path]
private lemma fkMedialLoopCount_twoLayer_twoToggle_eq_of_balance_eq
  {T : EvenTorus}
  {first second : T.Vertex}
-- given
  (source : Bool -> FKMedialLoopPairing T)
  (hbalance : FKMedialLayeredTwoCutBalance source first second) :
-- imply
  fkMedialLoopCount T (fkMedialTogglePairingAt (fkMedialTogglePairingAt (source false) first) second) + fkMedialLoopCount T (fkMedialTogglePairingAt (fkMedialTogglePairingAt (source true) first) second) = fkMedialLoopCount T (source false) + fkMedialLoopCount T (source true) := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCount_twoLayer_twoToggle_eq_of_balance source first second hbalance

/--
[fkMedialLayeredTwoCutBalance_of_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialLayeredCutBalance.lean)
-/
@[path]
private lemma fkMedialLayeredTwoCutBalance_of_alternating_eq
  {T : EvenTorus}
  {first second : T.Vertex}
-- given
  (source : Bool -> FKMedialLoopPairing T)
  (hfirst : FKMedialCutSplits (source false) first <-> Not (FKMedialCutSplits (source true) first))
  (halternating : forall layer, FKMedialAlternatingTwoCut (source layer) first second) :
-- imply
  FKMedialLayeredTwoCutBalance source first second := by
-- proof
  apply StatMech.FrontierD.fkMedialLayeredTwoCutBalance_of_alternating source first second hfirst halternating


-- created on 2026-10-23
