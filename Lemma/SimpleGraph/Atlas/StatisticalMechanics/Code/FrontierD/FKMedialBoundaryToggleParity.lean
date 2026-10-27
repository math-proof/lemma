import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
open Equiv StatMech StatMech.FrontierD


/--
[fkMedialBlackDart0_ne_dart1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean)
-/
@[path]
private lemma fkMedialBlackDart0_ne_dart1_eq
  {T : EvenTorus}
  {v : T.Vertex} :
-- imply
  fkMedialBlackDart0 v ≠ fkMedialBlackDart1 v := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDart0_ne_dart1 v

/--
[card_fkMedialBlackDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean)
-/
@[path]
private lemma card_fkMedialBlackDart_eq
  {T : EvenTorus}
  {T : EvenTorus} :
-- imply
  Fintype.card (FKMedialBlackDart T) = 2 * T.width * T.height := by
-- proof
  apply StatMech.FrontierD.card_fkMedialBlackDart T

/--
[fkMedialBlackDart_eq_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean)
-/
@[path]
private lemma fkMedialBlackDart_eq_zero_or_one_eq
  {T : EvenTorus}
  {d : FKMedialBlackDart T} :
-- imply
  d = fkMedialBlackDart0 d.1.1 \/ d = fkMedialBlackDart1 d.1.1 := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDart_eq_zero_or_one d

/--
[fkMedialBlackDartSwap_isSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean)
-/
@[path]
private lemma fkMedialBlackDartSwap_isSwap_eq
  {T : EvenTorus}
  {v : T.Vertex} :
-- imply
  (fkMedialBlackDartSwap v).IsSwap := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDartSwap_isSwap v

/--
[fkMedialBlackBoundaryPerm_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_toggle_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v) = fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartSwap v := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_toggle pairing v

/--
[fkMedialLoopCount_toggle_mod_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean)
-/
@[path]
private lemma fkMedialLoopCount_toggle_mod_two_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) % 2 = (fkMedialLoopCount T pairing + 1) % 2 := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCount_toggle_mod_two T pairing v

/--
[fkMedialTogglePairingAt_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean)
-/
@[path]
private lemma fkMedialTogglePairingAt_toggle_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing v) v = pairing := by
-- proof
  apply StatMech.FrontierD.fkMedialTogglePairingAt_toggle pairing v

/--
[fkMedialLoopCount_toggle_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialBoundaryToggleParity.lean)
-/
@[path]
private lemma fkMedialLoopCount_toggle_dichotomy_eq
  {T : EvenTorus}
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) + 1 = fkMedialLoopCount T pairing ∨ fkMedialLoopCount T pairing + 1 = fkMedialLoopCount T (fkMedialTogglePairingAt pairing v) := by
-- proof
  apply StatMech.FrontierD.fkMedialLoopCount_toggle_dichotomy T pairing v


-- created on 2026-10-23
