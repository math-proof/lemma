import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexStrandSlotBoundary.Part7
open StatMech StatMech.FrontierD


/--
[fkColoredBlackDartStrandSlot_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredBlackDartStrandSlot_injective_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T} :
-- imply
  Function.Injective (fkColoredBlackDartStrandSlot pairing) := by
-- proof
  apply StatMech.FrontierD.fkColoredBlackDartStrandSlot_injective pairing

/--
[fkColoredBlackDartStrandSlotEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredBlackDartStrandSlotEquiv_apply_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {dart : FKMedialBlackDart T} :
-- imply
  fkColoredBlackDartStrandSlotEquiv pairing dart = fkColoredBlackDartStrandSlot pairing dart := by
-- proof
  apply StatMech.FrontierD.fkColoredBlackDartStrandSlotEquiv_apply pairing dart

/--
[fkColoredBlackDartStrandSlot_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredBlackDartStrandSlot_toggle_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
  {dart : FKMedialBlackDart T} :
-- imply
  fkColoredBlackDartStrandSlot (fkMedialTogglePairingAt pairing v) dart = if fkMedialVertexParity v = true then fkColoredVertexStrandSlotSwap v (fkColoredBlackDartStrandSlot pairing dart) else fkColoredBlackDartStrandSlot pairing dart := by
-- proof
  apply StatMech.FrontierD.fkColoredBlackDartStrandSlot_toggle pairing v dart

/--
[fkColoredBlackDartStrandSlotEquiv_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredBlackDartStrandSlotEquiv_toggle_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkColoredBlackDartStrandSlotEquiv (fkMedialTogglePairingAt pairing v) = if fkMedialVertexParity v = true then (fkColoredBlackDartStrandSlotEquiv pairing).trans (fkColoredVertexStrandSlotSwap v) else fkColoredBlackDartStrandSlotEquiv pairing := by
-- proof
  apply StatMech.FrontierD.fkColoredBlackDartStrandSlotEquiv_toggle pairing v

/--
[fkColoredBlackDartStrandSlot_blackSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredBlackDartStrandSlot_blackSwap_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
  {dart : FKMedialBlackDart T} :
-- imply
  fkColoredBlackDartStrandSlotEquiv pairing (fkMedialBlackDartSwap v dart) = fkColoredVertexStrandSlotSwap v (fkColoredBlackDartStrandSlotEquiv pairing dart) := by
-- proof
  apply StatMech.FrontierD.fkColoredBlackDartStrandSlot_blackSwap pairing v dart

/--
[fkColoredStrandSlotBoundaryPerm_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredStrandSlotBoundaryPerm_toggle_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex} :
-- imply
  fkColoredStrandSlotBoundaryPerm (fkMedialTogglePairingAt pairing v) = if fkMedialVertexParity v = true then (fkColoredStrandSlotBoundaryPerm pairing).trans (fkColoredVertexStrandSlotSwap v) else (fkColoredVertexStrandSlotSwap v).trans (fkColoredStrandSlotBoundaryPerm pairing) := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSlotBoundaryPerm_toggle pairing v

/--
[FKColoredLoopPairing.color_blackDart_eq_slotColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma color_blackDart_eq_slotColor_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {layer : Bool}
  {dart : FKMedialBlackDart T} :
-- imply
  (source layer).color dart.1 = fkColoredLayeredSlotColor source (layer, fkColoredBlackDartStrandSlotEquiv (source layer).pairing dart) := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.color_blackDart_eq_slotColor source layer dart

/--
[FKColoredLoopPairing.slotColor_boundaryPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma slotColor_boundaryPerm_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {layer : Bool}
  {slot : T.Vertex × Bool} :
-- imply
  fkColoredLayeredSlotColor source (layer, fkColoredStrandSlotBoundaryPerm (source layer).pairing slot) = fkColoredLayeredSlotColor source (layer, slot) := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.slotColor_boundaryPerm source layer slot

/--
[fkColoredLayeredStrandSlotBoundaryPerm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredLayeredStrandSlotBoundaryPerm_apply_eq
  {T : EvenTorus}
  {slot : FKLayeredStrandSlot T}
-- given
  (pairing : Bool -> FKMedialLoopPairing T) :
-- imply
  fkColoredLayeredStrandSlotBoundaryPerm pairing slot = (slot.1, fkColoredStrandSlotBoundaryPerm (pairing slot.1) slot.2) := by
-- proof
  apply StatMech.FrontierD.fkColoredLayeredStrandSlotBoundaryPerm_apply pairing slot

/--
[fkColoredLayeredSlotColor_boundaryPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredLayeredSlotColor_boundaryPerm_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {slot : FKLayeredStrandSlot T} :
-- imply
  fkColoredLayeredSlotColor source (fkColoredLayeredStrandSlotBoundaryPerm (fun layer => (source layer).pairing) slot) = fkColoredLayeredSlotColor source slot := by
-- proof
  apply StatMech.FrontierD.fkColoredLayeredSlotColor_boundaryPerm source slot

/--
[fkColoredStrandSpliceRawColor_blackDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredStrandSpliceRawColor_blackDart_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T) :
-- imply
  fkColoredStrandSpliceRawColor source targetPairing slotEquiv (layer, dart.1) = fkColoredLayeredSlotColor source (slotEquiv (layer, fkColoredBlackDartStrandSlotEquiv (targetPairing layer) dart)) := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSpliceRawColor_blackDart source targetPairing slotEquiv layer dart

/--
[fkColoredStrandSpliceRawColor_blackBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredStrandSpliceRawColor_blackBoundary_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {n : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T)
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (hintertwines : FKColoredIndexedOccurrenceSlotIntertwining source targetPairing n key hinjective) :
-- imply
  fkColoredStrandSpliceRawColor source targetPairing (fkIndexedOccurrenceSlotEquiv n key hinjective) (layer, (fkMedialBlackBoundaryPerm (targetPairing layer) dart).1) = fkColoredStrandSpliceRawColor source targetPairing (fkIndexedOccurrenceSlotEquiv n key hinjective) (layer, dart.1) := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSpliceRawColor_blackBoundary source targetPairing n key hinjective hintertwines layer dart

/--
[fkColoredStrandSpliceRawColor_blackBoundary_of_slotColorInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma fkColoredStrandSpliceRawColor_blackBoundary_of_slotColorInvariant_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {n : Nat}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T)
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (hinvariant : FKColoredIndexedOccurrenceSlotColorInvariant source targetPairing n key hinjective) :
-- imply
  fkColoredStrandSpliceRawColor source targetPairing (fkIndexedOccurrenceSlotEquiv n key hinjective) (layer, (fkMedialBlackBoundaryPerm (targetPairing layer) dart).1) = fkColoredStrandSpliceRawColor source targetPairing (fkIndexedOccurrenceSlotEquiv n key hinjective) (layer, dart.1) := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSpliceRawColor_blackBoundary_of_slotColorInvariant source targetPairing n key hinjective hinvariant layer dart

/--
[coloredIndexedOccurrenceBoundaryIntertwining_of_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma coloredIndexedOccurrenceBoundaryIntertwining_of_slot_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {n : Nat}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T)
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (hintertwines : FKColoredIndexedOccurrenceSlotIntertwining source targetPairing n key hinjective) :
-- imply
  FKColoredIndexedOccurrenceBoundaryIntertwining source targetPairing n key hinjective := by
-- proof
  apply StatMech.FrontierD.coloredIndexedOccurrenceBoundaryIntertwining_of_slot source targetPairing n key hinjective hintertwines

/--
[coloredIndexedOccurrenceBoundaryIntertwining_of_slotColorInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma coloredIndexedOccurrenceBoundaryIntertwining_of_slotColorInvariant_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {n : Nat}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T)
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (hinvariant : FKColoredIndexedOccurrenceSlotColorInvariant source targetPairing n key hinjective) :
-- imply
  FKColoredIndexedOccurrenceBoundaryIntertwining source targetPairing n key hinjective := by
-- proof
  apply StatMech.FrontierD.coloredIndexedOccurrenceBoundaryIntertwining_of_slotColorInvariant source targetPairing n key hinjective hinvariant

/--
[coloredIndexedOccurrenceSlotIntertwining_of_successor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexStrandSlotBoundary.lean)
-/
@[path]
private lemma coloredIndexedOccurrenceSlotIntertwining_of_successor_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {n : Nat}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T)
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (next : Fin n -> Fin n)
  (htarget : forall layer i, fkColoredStrandSlotBoundaryPerm (targetPairing layer) (key layer i) = key layer (next i))
  (hsource : forall layer i, fkColoredStrandSlotBoundaryPerm (source layer).pairing (key layer i) = key layer (next i))
  (hfixed : forall layer slot, (¬ exists i, key layer i = slot) -> fkColoredStrandSlotBoundaryPerm (targetPairing layer) slot = fkColoredStrandSlotBoundaryPerm (source layer).pairing slot /\ (¬ exists i, key layer i = fkColoredStrandSlotBoundaryPerm (targetPairing layer) slot)) :
-- imply
  FKColoredIndexedOccurrenceSlotIntertwining source targetPairing n key hinjective := by
-- proof
  apply StatMech.FrontierD.coloredIndexedOccurrenceSlotIntertwining_of_successor source targetPairing n key hinjective next htarget hsource hfixed


-- created on 2026-10-23
