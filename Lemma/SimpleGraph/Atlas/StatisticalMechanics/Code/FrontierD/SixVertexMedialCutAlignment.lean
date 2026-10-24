import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexMedialCutAlignment
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkMedialCutSplits_iff_blackDartSwap_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMedialCutAlignment.lean)
-/
@[path]
private lemma fkMedialCutSplits_iff_blackDartSwap_sameCycle_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialBlackDart T} :
-- imply
  FKMedialCutSplits pairing d.1.1 <-> (fkMedialBlackBoundaryPerm pairing).SameCycle d (fkMedialBlackDartSwap d.1.1 d) := by
-- proof
  apply StatMech.FrontierD.fkMedialCutSplits_iff_blackDartSwap_sameCycle pairing d

/--
[fkMedialCutSplits_toggle_iff_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMedialCutAlignment.lean)
-/
@[path]
private lemma fkMedialCutSplits_toggle_iff_not_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  FKMedialCutSplits (fkMedialTogglePairingAt pairing v) v ↔ ¬FKMedialCutSplits pairing v := by
-- proof
  apply StatMech.FrontierD.fkMedialCutSplits_toggle_iff_not pairing v

/--
[fkMedialAlternatingTwoCut_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMedialCutAlignment.lean)
-/
@[path]
private lemma fkMedialAlternatingTwoCut_self_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  FKMedialAlternatingTwoCut pairing v v := by
-- proof
  apply StatMech.FrontierD.fkMedialAlternatingTwoCut_self pairing v

/--
[fkMedialLoopCount_twoToggle_eq_of_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMedialCutAlignment.lean)
-/
@[path]
private lemma fkMedialLoopCount_twoToggle_eq_of_alternating_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex}
-- given
  (halternating : FKMedialAlternatingTwoCut pairing first second) :
-- imply
  fkMedialLoopCount T (fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing first) second) = fkMedialLoopCount T pairing := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCount_twoToggle_eq_of_alternating pairing first second halternating

/--
[fkMedialLoopCount_toggle_add_toggle_eq_of_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMedialCutAlignment.lean)
-/
@[path]
private lemma fkMedialLoopCount_toggle_add_toggle_eq_of_opposite_eq
  {T : EvenTorus}
  {first second : FKMedialLoopPairing T}
  {v : T.Vertex}
-- given
  (hopposite : FKMedialCutSplits first v ↔ ¬FKMedialCutSplits second v) :
-- imply
  fkMedialLoopCount T (fkMedialTogglePairingAt first v) + fkMedialLoopCount T (fkMedialTogglePairingAt second v) = fkMedialLoopCount T first + fkMedialLoopCount T second := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCount_toggle_add_toggle_eq_of_opposite first second v hopposite

/--
[fkMedialAlternatingTwoCut_of_loopCount_twoToggle_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMedialCutAlignment.lean)
-/
@[path]
private lemma fkMedialAlternatingTwoCut_of_loopCount_twoToggle_eq_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex}
-- given
  (hcount : fkMedialLoopCount T (fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing first) second) = fkMedialLoopCount T pairing) :
-- imply
  FKMedialAlternatingTwoCut pairing first second := by
-- proof
  apply StatMech.FrontierD.fkMedialAlternatingTwoCut_of_loopCount_twoToggle_eq pairing first second hcount

/--
[fkMedialBlackBoundary_successors_alternate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMedialCutAlignment.lean)
-/
@[path]
private lemma fkMedialBlackBoundary_successors_alternate_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  let source := fkMedialBlackBoundaryPerm pairing let target := fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v) source.SameCycle (fkMedialBlackDart0 v) (fkMedialBlackDart1 v) ↔ ¬target.SameCycle (source (fkMedialBlackDart0 v)) (source (fkMedialBlackDart1 v)) := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundary_successors_alternate pairing v


-- created on 2026-10-23
