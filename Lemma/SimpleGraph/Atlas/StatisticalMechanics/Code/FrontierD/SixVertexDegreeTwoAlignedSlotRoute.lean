import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoAlignedSlotRoute.Part7
open StatMech StatMech.FrontierD


/--
[fkColoredSideSlot_eq_strandSlotOfBlackDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma fkColoredSideSlot_eq_strandSlotOfBlackDart_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {dart : FKMedialBlackDart T} :
-- imply
  fkColoredSideSlot (pairing dart.1.1) dart.1.2 = strandSlotOfBlackDart pairing dart := by
-- proof
  apply StatMech.FrontierD.fkColoredSideSlot_eq_strandSlotOfBlackDart pairing dart

/--
[strandSlotOfBlackDart_blackDartOfStrandSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma strandSlotOfBlackDart_blackDartOfStrandSlot_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {slot : T.Vertex × Bool} :
-- imply
  strandSlotOfBlackDart pairing (blackDartOfStrandSlot pairing slot) = slot.2 := by
-- proof
  apply StatMech.FrontierD.strandSlotOfBlackDart_blackDartOfStrandSlot pairing slot

/--
[fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {slot : T.Vertex × Bool} :
-- imply
  fkColoredBlackDartStrandSlotEquiv pairing (blackDartOfStrandSlot pairing slot) = slot := by
-- proof
  apply StatMech.FrontierD.fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot pairing slot

/--
[fkColoredVertexStrandSlotSwap_doubledAlignedSlot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma fkColoredVertexStrandSlotSwap_doubledAlignedSlot_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkColoredVertexStrandSlotSwap (doubledAlignedVertex x) (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) = (doubledAlignedVertex (doubledAlignedBranchSwap x), doubledAlignedSlot homega heta hdegree layer (doubledAlignedBranchSwap x)) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexStrandSlotSwap_doubledAlignedSlot homega heta hdegree layer x

/--
[fkMedialBlackDartSwap_doubledAlignedBlackDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma fkMedialBlackDartSwap_doubledAlignedBlackDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkMedialBlackDartSwap (doubledAlignedVertex x) (doubledAlignedBlackDart homega heta hdegree layer x) = doubledAlignedBlackDart homega heta hdegree layer (doubledAlignedBranchSwap x) := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDartSwap_doubledAlignedBlackDart homega heta hdegree layer x

/--
[blackSideIndex_boundaryAlignedSlotQRaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma blackSideIndex_boundaryAlignedSlotQRaw_eq
  {pairingP pairingQ vertexParity branch : Bool}
  {d : Fin 4} :
-- imply
  blackSideIndexOfStrandSlot vertexParity pairingQ (if branch then !boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d else boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) = if pairingP = pairingQ then blackSideIndexOfStrandSlot vertexParity pairingP (if branch then !strandSlot pairingP d else strandSlot pairingP d) else blackSideIndexOfStrandSlot vertexParity pairingP (if !branch then !strandSlot pairingP d else strandSlot pairingP d) := by
-- proof
  apply StatMech.FrontierD.blackSideIndex_boundaryAlignedSlotQRaw pairingP pairingQ vertexParity branch d

/--
[doubledAlignedBlackDart_true_eq_false_or_branchSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma doubledAlignedBlackDart_true_eq_false_or_branchSwap_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  let retie := orientedDartAlignedRetie homega heta hdegree x.1 doubledAlignedBlackDart homega heta hdegree true x = if retie.pairingP = retie.pairingQ then doubledAlignedBlackDart homega heta hdegree false x else doubledAlignedBlackDart homega heta hdegree false (doubledAlignedBranchSwap x) := by
-- proof
  apply StatMech.FrontierD.doubledAlignedBlackDart_true_eq_false_or_branchSwap homega heta hdegree x

/--
[sixVertexDegreeTwoAlignedBoundaryKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundaryKey_injective_eq
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
  Function.Injective (sixVertexDegreeTwoAlignedBoundaryKey homega heta hdegree middle homegaSector hetaSector hmiddle layer) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundaryKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoAlignedBoundaryFinKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundaryFinKey_injective_eq
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
  Function.Injective (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle layer

/--
[sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree false dart = fkColoredBlackDartStrandSlotEquiv (alignedRoutingLoopPairing homega heta hdegree false) dart := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false homega heta hdegree dart

/--
[sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree true dart = fkColoredBlackDartStrandSlotEquiv (alignedRoutingLoopPairing homega heta hdegree true) (alignedBlackDartLayerSwap homega heta hdegree dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true homega heta hdegree dart

/--
[sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {layer : Bool}
  {i : Fin (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle))}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer i = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer ((Fintype.equivFin (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)).symm i).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart homega heta hdegree middle homegaSector hetaSector hmiddle layer i

/--
[sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff_dart_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff_dart_mem_eq
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
  (exists i, sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer i = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) <-> dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff_dart_mem homega heta hdegree middle homegaSector hetaSector hmiddle layer dart

/--
[sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart_eq
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
  (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle)) :
-- imply
  fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree (!layer) dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart

/--
[sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart_of_not_mem_eq
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
  (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle)) :
-- imply
  fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart_of_not_mem homega heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart

/--
[sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff_eq
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
  (exists i, sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer i = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) ↔ x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoAlignedBoundaryFinKey_selectedState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedBoundaryFinKey_selectedState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
  {x : DoubledAlignedState omega eta}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle) :
-- imply
  sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle layer (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree middle homegaSector hetaSector hmiddle x hx) = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedBoundaryFinKey_selectedState homega heta hdegree middle homegaSector hetaSector hmiddle x hx layer

/--
[sixVertexDegreeTwoAlignedColoredSource_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_arrows_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree layer).arrows = if layer then eta else omega := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_arrows homega heta hdegree layer

/--
[sixVertexDegreeTwoAlignedColoredSource_slotColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_slotColor_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {v : T.Vertex}
  {slot : Bool}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, v, slot) = (fkMedialVertexParity v ^^ horizontalSlot (sixVertexLocalIncomingPattern (if layer then eta else omega) v) slot) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_slotColor homega heta hdegree layer v slot

/--
[sixVertexDegreeTwoAlignedColoredSource_doubledDart_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_doubledDart_color_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree layer).color (doubledAlignedBlackDart homega heta hdegree layer x).1) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_doubledDart_color homega heta hdegree layer x

/--
[sixVertexDegreeTwoAlignedColoredSource_falseDart_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_falseDart_color_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color (doubledAlignedBlackDart homega heta hdegree false x).1) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (false, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree false x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_falseDart_color homega heta hdegree x

/--
[sixVertexDegreeTwoAlignedColoredSource_falseDart_true_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_falseDart_true_color_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  let retie := orientedDartAlignedRetie homega heta hdegree x.1 ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree true).color (doubledAlignedBlackDart homega heta hdegree false x).1) = if retie.pairingP = retie.pairingQ then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree true x) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, doubledAlignedVertex (doubledAlignedBranchSwap x), doubledAlignedSlot homega heta hdegree true (doubledAlignedBranchSwap x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_falseDart_true_color homega heta hdegree x

/--
[FKColoredLoopPairing.color_blackBoundaryPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma color_blackBoundaryPerm_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairing T}
  {dart : FKMedialBlackDart T} :
-- imply
  source.color (fkMedialBlackBoundaryPerm source.pairing dart).1 = source.color dart.1 := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.color_blackBoundaryPerm source dart

/--
[FKColoredLoopPairing.color_blackBoundaryPerm_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma color_blackBoundaryPerm_pow_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairing T}
  {dart : FKMedialBlackDart T}
  {k : Nat} :
-- imply
  source.color ((fkMedialBlackBoundaryPerm source.pairing ^ k) dart).1 = source.color dart.1 := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.color_blackBoundaryPerm_pow source dart k

/--
[sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
  {k : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree layer).color ((alignedBoundaryPerm homega heta hdegree layer ^ k) (doubledAlignedBlackDart homega heta hdegree layer x)).1) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color homega heta hdegree layer x k

/--
[sixVertexDegreeTwoAlignedColoredSource_boundarySegment_slotColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_boundarySegment_slotColor_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
  {dart : FKMedialBlackDart T}
  {k : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hk : k < finiteFirstReturnTime (alignedBoundaryPerm homega heta hdegree false) (activeBlackDart (omega := omega) (eta := eta)) (doubledAlignedBlackDartEquiv homega heta hdegree false x))
  (hpow : (alignedBoundaryPerm homega heta hdegree false ^ k) (doubledAlignedBlackDart homega heta hdegree false x) = dart) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_boundarySegment_slotColor homega heta hdegree layer x dart k hk hpow

/--
[sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (false, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree false x) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (false, doubledAlignedVertex (doubledAlignedFirstReturnPerm homega heta hdegree x), doubledAlignedSlot homega heta hdegree false (doubledAlignedFirstReturnPerm homega heta hdegree x)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false homega heta hdegree x

/--
[sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_true_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x let retie := orientedDartAlignedRetie homega heta hdegree y.1 fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree true x) = if retie.pairingP = retie.pairingQ then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, doubledAlignedVertex y, doubledAlignedSlot homega heta hdegree true y) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, doubledAlignedVertex (doubledAlignedBranchSwap y), doubledAlignedSlot homega heta hdegree true (doubledAlignedBranchSwap y)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_true homega heta hdegree x

/--
[sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {dart : FKMedialBlackDart T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (false, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree false dart) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree true dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq homega heta hdegree dart hinactive

/--
[sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  let retie := orientedDartAlignedRetie homega heta hdegree x.1 (fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (false, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree false x) != fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree true x)) = if x.2 then (retie.pairingP != retie.pairingQ) && (fkMedialVertexParity (doubledAlignedVertex x) != sideVertical x.1.1.1.2) else (retie.pairingP == retie.pairingQ) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne homega heta hdegree x

/--
[sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hne : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP != (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) :
-- imply
  (fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree true x) != fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, doubledAlignedVertex (doubledAlignedBranchSwap x), doubledAlignedSlot homega heta hdegree true (doubledAlignedBranchSwap x))) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne homega heta hdegree x hne

/--
[sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne_of_false_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne_of_false_eq_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {x : DoubledAlignedState omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hfalse : fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (false, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree false x) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (false, doubledAlignedVertex (doubledAlignedBranchSwap x), doubledAlignedSlot homega heta hdegree false (doubledAlignedBranchSwap x))) :
-- imply
  (fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree true x) != fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (true, doubledAlignedVertex (doubledAlignedBranchSwap x), doubledAlignedSlot homega heta hdegree true (doubledAlignedBranchSwap x))) = true := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne_of_false_eq homega heta hdegree x hfalse

/--
[sixVertexDegreeTwoAlignedTransportedColor_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTransportedColor_active_eq
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
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle homegaSector hetaSector hmiddle)) (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle homegaSector hetaSector hmiddle) (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree middle homegaSector hetaSector hmiddle) (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) = if _hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle homegaSector hetaSector hmiddle then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (!layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree (!layer) x) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTransportedColor_active homega heta hdegree middle homegaSector hetaSector hmiddle layer x

/--
[sixVertexDegreeTwoAlignedTargetPairing_of_left_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTargetPairing_of_left_empty_eq
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
  (hmiddle : 0 < middle)
  (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutLeft = []) :
-- imply
  sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer = alignedRoutingLoopPairing homega heta hdegree layer := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTargetPairing_of_left_empty homega heta hdegree middle homegaSector hetaSector hmiddle hleft layer

/--
[sixVertexDegreeTwoAlignedTargetPairing_of_right_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoAlignedSlotRoute.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAlignedTargetPairing_of_right_empty_eq
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
  (hmiddle : 0 < middle)
  (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle homegaSector hetaSector hmiddle).cutRight = []) :
-- imply
  sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle homegaSector hetaSector hmiddle layer = alignedRoutingLoopPairing homega heta hdegree layer := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAlignedTargetPairing_of_right_empty homega heta hdegree middle homegaSector hetaSector hmiddle hright layer


-- created on 2026-10-23
