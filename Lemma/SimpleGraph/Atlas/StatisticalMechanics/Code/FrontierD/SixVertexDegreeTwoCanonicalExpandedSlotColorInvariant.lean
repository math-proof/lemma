import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.Part5
open StatMech StatMech.FrontierD


/--
[fkMedialTogglePairingAt_two_eq_toggleMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma fkMedialTogglePairingAt_two_eq_toggleMask_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex}
-- given
  (hne : first ≠ second) :
-- imply
  fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing first) second = fkMedialTogglePairingMask pairing (fun v => decide (v = first) || decide (v = second)) := by
-- proof
  apply StatMech.FrontierD.fkMedialTogglePairingAt_two_eq_toggleMask pairing first second hne

/--
[sixVertexDegreeTwoAlignedTargetPairing_eq_toggleMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTargetPairing_eq_toggleMask_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer = fkMedialTogglePairingMask (alignedRoutingLoopPairing homega heta hdegree layer) (sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTargetPairing_eq_toggleMask homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[fkMedialTogglePairingMask_compose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma fkMedialTogglePairingMask_compose_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
-- given
  (first second : T.Vertex -> Bool) :
-- imply
  fkMedialTogglePairingMask (fkMedialTogglePairingMask pairing first) second = fkMedialTogglePairingMask pairing (fun v => first v != second v) := by
-- proof
  apply StatMech.FrontierD.fkMedialTogglePairingMask_compose pairing first second

/--
[sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer = fkMedialTogglePairingMask (alignedRoutingLoopPairing homega heta hdegree layer) (fun v => sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle homegaSector hetaSector hmiddle v != sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle homegaSector hetaSector hmiddle layer v) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoCanonicalCorrectionMask_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalCorrectionMask_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hactive : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 2) :
-- imply
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle homegaSector hetaSector hmiddle v let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle homegaSector hetaSector hmiddle v sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle homegaSector hetaSector hmiddle layer v = ((transition && !selected) || (selected && ((orientedDartAlignedRetie homega heta hdegree d).pairingP != (orientedDartAlignedRetie homega heta hdegree d).pairingQ))) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalCorrectionMask_active homega heta hdegree middle homegaSector hetaSector hmiddle layer v hactive

/--
[sixVertexDegreeTwoCanonicalCorrectionMask_layer_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalCorrectionMask_layer_independent_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {first second : Bool}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle homegaSector hetaSector hmiddle first v = sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle homegaSector hetaSector hmiddle second v := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalCorrectionMask_layer_independent homega heta hdegree middle homegaSector hetaSector hmiddle first second v

/--
[sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hactive : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 2) :
-- imply
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive let retie := orientedDartAlignedRetie homega heta hdegree d let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle homegaSector hetaSector hmiddle v let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle homegaSector hetaSector hmiddle v (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle false v, sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle true v) = (if selected then if transition then !retie.pairingQ else retie.pairingQ else retie.pairingP, if selected then if transition then !retie.pairingP else retie.pairingP else retie.pairingQ) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table homega heta hdegree middle homegaSector hetaSector hmiddle v hactive

/--
[sixVertexDegreeTwoCanonicalExpandedTargetPairing_emptyCut_regression](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedTargetPairing_emptyCut_regression_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hactive : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 2)
  (hempty : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft = [] \/ (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight = [])
  (hselected : sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle homegaSector hetaSector hmiddle v = true)
  (hmismatch : let d := orientedDisagreementDartAtActiveVertex homega heta v hactive (orientedDartAlignedRetie homega heta hdegree d).pairingP != (orientedDartAlignedRetie homega heta hdegree d).pairingQ = true) :
-- imply
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive let retie := orientedDartAlignedRetie homega heta hdegree d (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle false v, sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle true v) = (retie.pairingQ, retie.pairingP) /\ (retie.pairingP != retie.pairingQ) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedTargetPairing_emptyCut_regression homega heta hdegree middle homegaSector hetaSector hmiddle v hactive hempty hselected hmismatch

/--
[sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  fkMedialTogglePairingMask (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) (sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle homegaSector hetaSector hmiddle layer) = sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoCanonicalExpandedTargetBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedTargetBoundary_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  fkColoredStrandSlotBoundaryPerm (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) = (fkColoredParityMaskStrandSlotSwap (sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer) false).trans ((fkColoredStrandSlotBoundaryPerm (alignedRoutingLoopPairing homega heta hdegree layer)).trans (fkColoredParityMaskStrandSlotSwap (sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer) true)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedTargetBoundary homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoCanonicalExpandedTargetBoundary_slotOfFalseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedTargetBoundary_slotOfFalseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  fkColoredStrandSlotBoundaryPerm (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedTargetBoundary_slotOfFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart

/--
[sixVertexDegreeTwoCanonicalExpandedSlotColorInvariant_of_falseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedSlotColorInvariant_of_falseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hfalseDart : forall (layer : Bool) (dart : FKMedialBlackDart T), fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart))) :
-- imply
  FKColoredIndexedOccurrenceSlotColorInvariant (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle) (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedSlotColorInvariant_of_falseDart homega heta hdegree middle homegaSector hetaSector hmiddle hfalseDart

/--
[sixVertexDegreeTwoCanonicalExpandedRecoverPairing_eq_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoCanonicalExpandedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoCanonicalExpandedRecoverPairing_eq_source_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoCanonicalExpandedRecoverPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer = alignedRoutingLoopPairing homega heta hdegree layer := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoCanonicalExpandedRecoverPairing_eq_source homega heta hdegree middle homegaSector hetaSector hmiddle layer


-- created on 2026-10-23
