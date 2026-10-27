import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant.Part10
open StatMech StatMech.FrontierD


/--
[mem_sixVertexDegreeTwoBranchClosedUnitPrefix_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma mem_sixVertexDegreeTwoBranchClosedUnitPrefix_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle ↔ x.1 ∈ sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexDegreeTwoBranchClosedUnitPrefix_iff homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  doubledAlignedBranchSwap x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle ↔ x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[sixVertexDegreeTwoBranchClosedUnitPrefix_charge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedUnitPrefix_charge_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  ((sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle).map (doubledAlignedCharge hdegree)).sum = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedUnitPrefix_charge homega heta hdegree middle homegaSector hetaSector hmiddle

/--
[sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective_eq
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
  Function.Injective (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoBranchClosedBoundaryFinKey_exists_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedBoundaryFinKey_exists_iff_eq
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
  (exists i, sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer i = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) ↔ dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedBoundaryFinKey_exists_iff homega heta hdegree middle homegaSector hetaSector hmiddle layer dart

/--
[sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart_eq
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
  (hmiddle : 0 < middle)
  (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle)) :
-- imply
  fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree (!layer) dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart

/--
[sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart_of_not_mem_eq
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
  (hmiddle : 0 < middle)
  (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle)) :
-- imply
  fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart_of_not_mem homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart

/--
[sixVertexDegreeTwoBranchClosedBoundarySegments_branchSwap_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedBoundarySegments_branchSwap_mem_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  doubledAlignedBlackDart homega heta hdegree false (doubledAlignedBranchSwap x) ∈ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle) ↔ doubledAlignedBlackDart homega heta hdegree false x ∈ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedBoundarySegments_branchSwap_mem_iff homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[sixVertexDegreeTwoBranchClosedSelected_branchSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedSelected_branchSwap_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedBranchSwap x) = sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle homegaSector hetaSector hmiddle x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedSelected_branchSwap homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[fkMedialBlackDartSwap_self_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkMedialBlackDartSwap_self_vertex_eq
  {T : EvenTorus}
  {dart : FKMedialBlackDart T} :
-- imply
  (fkMedialBlackDartSwap dart.1.1 dart).1.1 = dart.1.1 := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDartSwap_self_vertex dart

/--
[fkColoredParityMaskStrandSlotSwap_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkColoredParityMaskStrandSlotSwap_self_eq
  {T : EvenTorus}
  {parity : Bool}
  {slot : T.Vertex × Bool}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  fkColoredParityMaskStrandSlotSwap mask parity (fkColoredParityMaskStrandSlotSwap mask parity slot) = slot := by
-- proof
  apply StatMech.FrontierD.fkColoredParityMaskStrandSlotSwap_self mask parity slot

/--
[fkColoredParityMaskStrandSlotSwap_apply_of_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkColoredParityMaskStrandSlotSwap_apply_of_true_eq
  {T : EvenTorus}
  {parity : Bool}
  {slot : T.Vertex × Bool}
-- given
  (mask : T.Vertex -> Bool)
  (hselected : (mask slot.1 && (fkMedialVertexParity slot.1 == parity)) = true) :
-- imply
  fkColoredParityMaskStrandSlotSwap mask parity slot = fkColoredVertexStrandSlotSwap slot.1 slot := by
-- proof
  apply StatMech.FrontierD.fkColoredParityMaskStrandSlotSwap_apply_of_true mask parity slot hselected

/--
[fkColoredParityMaskStrandSlotSwap_apply_of_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkColoredParityMaskStrandSlotSwap_apply_of_false_eq
  {T : EvenTorus}
  {parity : Bool}
  {slot : T.Vertex × Bool}
-- given
  (mask : T.Vertex -> Bool)
  (hunselected : (mask slot.1 && (fkMedialVertexParity slot.1 == parity)) = false) :
-- imply
  fkColoredParityMaskStrandSlotSwap mask parity slot = slot := by
-- proof
  apply StatMech.FrontierD.fkColoredParityMaskStrandSlotSwap_apply_of_false mask parity slot hunselected

/--
[fkMedialBlackBoundaryPerm_togglePairingMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkMedialBlackBoundaryPerm_togglePairingMask_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  fkMedialBlackBoundaryPerm (fkMedialTogglePairingMask pairing mask) = fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartMaskSwap mask := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackBoundaryPerm_togglePairingMask pairing mask

/--
[fkColoredBlackDartStrandSlotEquiv_togglePairingMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkColoredBlackDartStrandSlotEquiv_togglePairingMask_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  fkColoredBlackDartStrandSlotEquiv (fkMedialTogglePairingMask pairing mask) = (fkColoredBlackDartStrandSlotEquiv pairing).trans (fkColoredParityMaskStrandSlotSwap mask true) := by
-- proof
  apply StatMech.FrontierD.fkColoredBlackDartStrandSlotEquiv_togglePairingMask pairing mask

/--
[fkColoredBlackDartStrandSlotEquiv_blackDartMaskSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkColoredBlackDartStrandSlotEquiv_blackDartMaskSwap_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {dart : FKMedialBlackDart T}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  fkColoredBlackDartStrandSlotEquiv pairing (fkMedialBlackDartMaskSwap mask dart) = fkColoredParityMaskStrandSlotSwap mask false (fkColoredParityMaskStrandSlotSwap mask true (fkColoredBlackDartStrandSlotEquiv pairing dart)) := by
-- proof
  apply StatMech.FrontierD.fkColoredBlackDartStrandSlotEquiv_blackDartMaskSwap pairing mask dart

/--
[fkColoredStrandSlotBoundaryPerm_togglePairingMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkColoredStrandSlotBoundaryPerm_togglePairingMask_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  fkColoredStrandSlotBoundaryPerm (fkMedialTogglePairingMask pairing mask) = (fkColoredParityMaskStrandSlotSwap mask false).trans ((fkColoredStrandSlotBoundaryPerm pairing).trans (fkColoredParityMaskStrandSlotSwap mask true)) := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSlotBoundaryPerm_togglePairingMask pairing mask

/--
[fkMedialTogglePairingMask_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkMedialTogglePairingMask_self_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  fkMedialTogglePairingMask (fkMedialTogglePairingMask pairing mask) mask = pairing := by
-- proof
  apply StatMech.FrontierD.fkMedialTogglePairingMask_self pairing mask

/--
[sixVertexDegreeTwoBranchClosedExpandedTargetBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedExpandedTargetBoundary_eq
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
  fkColoredStrandSlotBoundaryPerm (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) = (fkColoredParityMaskStrandSlotSwap (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer) false).trans ((fkColoredStrandSlotBoundaryPerm (alignedRoutingLoopPairing homega heta hdegree layer)).trans (fkColoredParityMaskStrandSlotSwap (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer) true)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedExpandedTargetBoundary homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoBranchClosedExpandedTargetPairing_recover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedExpandedTargetPairing_recover_eq
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
  fkMedialTogglePairingMask (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer) = alignedRoutingLoopPairing homega heta hdegree layer := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedExpandedTargetPairing_recover homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive_eq
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
  (hzero : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 0) :
-- imply
  sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer v = false := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer v hzero

/--
[sixVertexDegreeTwoBranchClosedExpandedTargetPairing_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedExpandedTargetPairing_inactive_eq
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
  (hzero : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 0) :
-- imply
  sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer v = alignedRoutingLoopPairing homega heta hdegree layer v := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedExpandedTargetPairing_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer v hzero

/--
[sixVertexDegreeTwoBranchClosedExpandedTargetPairing_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedExpandedTargetPairing_active_eq
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
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive let transition := sixVertexDegreeTwoBranchClosedTransitionVertex homega heta hdegree middle homegaSector hetaSector hmiddle v let internal := sixVertexDegreeTwoBranchClosedInternalMismatchVertex homega heta hdegree middle homegaSector hetaSector hmiddle v sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer v = if transition := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedExpandedTargetPairing_active homega heta hdegree middle homegaSector hetaSector hmiddle layer v hactive

/--
[sixVertexDegreeTwoBranchClosedTransportedColor_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedTransportedColor_dart_eq
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
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) = if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle) then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree (!layer) dart) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedTransportedColor_dart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart

/--
[sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (doubledAlignedBlackDart homega heta hdegree false x) = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active homega heta hdegree layer x

/--
[sixVertexDegreeTwoBranchClosedTransportedColor_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedTransportedColor_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) = if _hx : x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (!layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree (!layer) x) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedTransportedColor_active homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoBranchClosedTransportedColor_dart_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedTransportedColor_dart_of_inactive_eq
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
  (hmiddle : 0 < middle)
  (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedTransportedColor_dart_of_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hinactive

/--
[sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkColoredStrandSlotBoundaryPerm (alignedRoutingLoopPairing homega heta hdegree layer) (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (if layer then (alignedBlackDartLayerSwap homega heta hdegree).symm (alignedBoundaryPerm homega heta hdegree false dart) else alignedBoundaryPerm homega heta hdegree false dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart homega heta hdegree layer dart

/--
[sixVertexDegreeTwoAlignedTrueFirstReturn_arrival](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTrueFirstReturn_arrival_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  finiteFirstReturn (alignedBoundaryPerm homega heta hdegree true) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree true x) = doubledAlignedBlackDartEquiv homega heta hdegree true (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTrueFirstReturn_arrival homega heta hdegree x

/--
[sixVertexDegreeTwoBranchClosedSelected_trueFirstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedSelected_trueFirstReturn_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle homegaSector hetaSector hmiddle (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x) = sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle homegaSector hetaSector hmiddle (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedSelected_trueFirstReturn homega heta hdegree middle homegaSector hetaSector hmiddle x

/--
[sixVertexDegreeTwoAlignedFalseDartSlotSwap_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedFalseDartSlotSwap_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {parity layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (mask : T.Vertex -> Bool) :
-- imply
  sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree mask parity layer (doubledAlignedBlackDart homega heta hdegree false x) = if mask (doubledAlignedVertex x) && (fkMedialVertexParity (doubledAlignedVertex x) == parity) then doubledAlignedBlackDart homega heta hdegree false (doubledAlignedBranchSwap x) else doubledAlignedBlackDart homega heta hdegree false x := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedFalseDartSlotSwap_active homega heta hdegree mask parity layer x

/--
[sixVertexDegreeTwoBranchClosedFalseDartSlotSwap_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedFalseDartSlotSwap_mem_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {parity layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree middle homegaSector hetaSector hmiddle layer) parity layer dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle) ↔ dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedFalseDartSlotSwap_mem_iff homega heta hdegree middle homegaSector hetaSector hmiddle parity layer dart

/--
[alignedBlackDartLayerSwap_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma alignedBlackDartLayerSwap_vertex_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (alignedBlackDartLayerSwap homega heta hdegree dart).1.1 = dart.1.1 := by
-- proof
  apply StatMech.FrontierD.alignedBlackDartLayerSwap_vertex homega heta hdegree dart

/--
[alignedBlackDartLayerSwap_symm_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma alignedBlackDartLayerSwap_symm_vertex_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  ((alignedBlackDartLayerSwap homega heta hdegree).symm dart).1.1 = dart.1.1 := by
-- proof
  apply StatMech.FrontierD.alignedBlackDartLayerSwap_symm_vertex homega heta hdegree dart

/--
[alignedBlackDartLayerSwap_symm_false_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma alignedBlackDartLayerSwap_symm_false_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  let retie := orientedDartAlignedRetie homega heta hdegree x.1 (alignedBlackDartLayerSwap homega heta hdegree).symm (doubledAlignedBlackDart homega heta hdegree false x) = doubledAlignedBlackDart homega heta hdegree false (if retie.pairingP = retie.pairingQ then x else doubledAlignedBranchSwap x) := by
-- proof
  apply StatMech.FrontierD.alignedBlackDartLayerSwap_symm_false_active homega heta hdegree x

/--
[sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart).1 = dart.1.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst homega heta hdegree layer dart

/--
[fkColoredParityMaskStrandSlotSwap_slotOfFalseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkColoredParityMaskStrandSlotSwap_slotOfFalseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {parity layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (mask : T.Vertex -> Bool) :
-- imply
  fkColoredParityMaskStrandSlotSwap mask parity (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree mask parity layer dart) := by
-- proof
  apply StatMech.FrontierD.fkColoredParityMaskStrandSlotSwap_slotOfFalseDart homega heta hdegree mask parity layer dart

/--
[sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart_of_inactive_eq
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
  (hmiddle : 0 < middle)
  (hdart : Not (activeBlackDart (omega := omega) (eta := eta) dart))
  (hnext : Not (activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart))) :
-- imply
  sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart = alignedBoundaryPerm homega heta hdegree false dart := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart_of_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart hnext

/--
[sixVertexDegreeTwoBranchClosedExpandedTargetBoundary_slotOfFalseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedExpandedTargetBoundary_slotOfFalseDart_eq
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
  fkColoredStrandSlotBoundaryPerm (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedExpandedTargetBoundary_slotOfFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart

/--
[sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {slot : T.Vertex × Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoAlignedFalseDartOfSlot homega heta hdegree layer slot) = slot := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse homega heta hdegree layer slot

/--
[sixVertexDegreeTwoBranchClosedSlotColorInvariant_of_falseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedSlotColorInvariant_of_falseDart_eq
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
  (hfalseDart : forall (layer : Bool) (dart : FKMedialBlackDart T), fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart))) :
-- imply
  FKColoredIndexedOccurrenceSlotColorInvariant (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle) (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedSlotColorInvariant_of_falseDart homega heta hdegree middle homegaSector hetaSector hmiddle hfalseDart

/--
[fkColoredVertexStrandSlotSwap_apply_of_fst_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkColoredVertexStrandSlotSwap_apply_of_fst_ne_eq
  {T : EvenTorus}
  {v : T.Vertex}
  {slot : T.Vertex × Bool}
-- given
  (hne : slot.1 ≠ v) :
-- imply
  fkColoredVertexStrandSlotSwap v slot = slot := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexStrandSlotSwap_apply_of_fst_ne v slot hne

/--
[fkColoredStrandSlotBoundaryPerm_retie_apply_of_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma fkColoredStrandSlotBoundaryPerm_retie_apply_of_away_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {first second : T.Vertex}
  {slot : T.Vertex × Bool}
-- given
  (hfirst : if fkMedialVertexParity first = true then (fkColoredStrandSlotBoundaryPerm pairing slot).1 ≠ first else slot.1 ≠ first)
  (hsecond : if fkMedialVertexParity second = true then (fkColoredStrandSlotBoundaryPerm pairing slot).1 ≠ second else slot.1 ≠ second) :
-- imply
  fkColoredStrandSlotBoundaryPerm (sixVertexRetieAtTransitionVertices pairing first second) slot = fkColoredStrandSlotBoundaryPerm pairing slot := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSlotBoundaryPerm_retie_apply_of_away pairing first second slot hfirst hsecond

/--
[sixVertexDegreeTwoAlignedTargetBoundary_apply_of_away](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTargetBoundary_apply_of_away_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {slot : T.Vertex × Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight ≠ [])
  (hrightAway : let rightVertex := doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight.head hright) if fkMedialVertexParity rightVertex = true then (fkColoredStrandSlotBoundaryPerm (alignedRoutingLoopPairing homega heta hdegree layer) slot).1 ≠ rightVertex else slot.1 ≠ rightVertex)
  (hleftAway : let leftVertex := doubledAlignedVertex ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft.head hleft) if fkMedialVertexParity leftVertex = true then (fkColoredStrandSlotBoundaryPerm (alignedRoutingLoopPairing homega heta hdegree layer) slot).1 ≠ leftVertex else slot.1 ≠ leftVertex) :
-- imply
  fkColoredStrandSlotBoundaryPerm (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer) slot = fkColoredStrandSlotBoundaryPerm (alignedRoutingLoopPairing homega heta hdegree layer) slot := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTargetBoundary_apply_of_away homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer slot hrightAway hleftAway

/--
[sixVertexDegreeTwoAlignedTransportedColor_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTransportedColor_dart_eq
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
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) = if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree (!layer) dart) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTransportedColor_dart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart

/--
[sixVertexDegreeTwoAlignedTransportedColor_dart_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTransportedColor_dart_of_inactive_eq
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
  (hmiddle : 0 < middle)
  (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTransportedColor_dart_of_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hinactive

/--
[sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart))) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (alignedBoundaryPerm homega heta hdegree false dart)) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color homega heta hdegree layer dart hinactive

/--
[sixVertexDegreeTwoBranchClosedExpanded_falseDart_color_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoBranchClosedExpanded_falseDart_color_of_inactive_eq
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
  (hmiddle : 0 < middle)
  (hdart : Not (activeBlackDart (omega := omega) (eta := eta) dart))
  (hnext : Not (activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart))) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoBranchClosedExpanded_falseDart_color_of_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart hnext

/--
[sixVertexDegreeTwoAlignedTransportedColor_falseBoundary_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTransportedColor_falseBoundary_of_inactive_eq
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
  (hmiddle : 0 < middle)
  (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart))) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (alignedBoundaryPerm homega heta hdegree false dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTransportedColor_falseBoundary_of_inactive homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hinactive

/--
[doubledAlignedBoundarySegments_step_mem_iff_of_state_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotColorInvariant.lean)
-/
@[path]
private lemma doubledAlignedBoundarySegments_step_mem_iff_of_state_invariant_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {states : List (DoubledAlignedState omega eta)}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hinvariant : forall y : DoubledAlignedState omega eta, y ∈ states ↔ (doubledAlignedFirstReturnPerm homega heta hdegree).symm y ∈ states) :
-- imply
  alignedBoundaryPerm homega heta hdegree false dart ∈ doubledAlignedBoundarySegments homega heta hdegree false states ↔ dart ∈ doubledAlignedBoundarySegments homega heta hdegree false states := by
-- proof
  apply StatMech.FrontierD.doubledAlignedBoundarySegments_step_mem_iff_of_state_invariant homega heta hdegree states hinvariant dart


-- created on 2026-10-23
