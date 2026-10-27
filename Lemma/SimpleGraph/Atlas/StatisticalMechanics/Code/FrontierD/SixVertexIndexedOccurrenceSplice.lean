import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexIndexedOccurrenceSplice.Part2
open StatMech StatMech.FrontierD


/--
[fkIndexedOccurrenceSlotEquiv_apply_key](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexIndexedOccurrenceSplice.lean)
-/
@[path]
private lemma fkIndexedOccurrenceSlotEquiv_apply_key_eq
  {T : EvenTorus}
  {n : Nat}
  {layer : Bool}
  {i : Fin n}
-- given
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer)) :
-- imply
  fkIndexedOccurrenceSlotEquiv n key hinjective (layer, key layer i) = (!layer, key (!layer) i) := by
-- proof
  apply StatMech.FrontierD.fkIndexedOccurrenceSlotEquiv_apply_key n key hinjective layer i

/--
[fkIndexedOccurrenceSlotEquiv_apply_of_not_routed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexIndexedOccurrenceSplice.lean)
-/
@[path]
private lemma fkIndexedOccurrenceSlotEquiv_apply_of_not_routed_eq
  {T : EvenTorus}
  {n : Nat}
  {slot : FKLayeredStrandSlot T}
-- given
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (hslot : ¬ exists i : Fin n, key slot.1 i = slot.2) :
-- imply
  fkIndexedOccurrenceSlotEquiv n key hinjective slot = slot := by
-- proof
  apply StatMech.FrontierD.fkIndexedOccurrenceSlotEquiv_apply_of_not_routed n key hinjective slot hslot

/--
[fkIndexedOccurrenceSlotEquiv_apply_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexIndexedOccurrenceSplice.lean)
-/
@[path]
private lemma fkIndexedOccurrenceSlotEquiv_apply_self_eq
  {T : EvenTorus}
  {n : Nat}
  {slot : FKLayeredStrandSlot T}
-- given
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer)) :
-- imply
  fkIndexedOccurrenceSlotEquiv n key hinjective (fkIndexedOccurrenceSlotEquiv n key hinjective slot) = slot := by
-- proof
  apply StatMech.FrontierD.fkIndexedOccurrenceSlotEquiv_apply_self n key hinjective slot

/--
[FKColoredStrandSplice.ofIndexedOccurrences_slotEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexIndexedOccurrenceSplice.lean)
-/
@[path]
private lemma ofIndexedOccurrences_slotEquiv_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {n : Nat}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T)
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining source targetPairing n key hinjective) :
-- imply
  (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing n key hinjective hboundary).slotEquiv = fkIndexedOccurrenceSlotEquiv n key hinjective := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.ofIndexedOccurrences_slotEquiv source targetPairing n key hinjective hboundary

/--
[FKColoredStrandSplice.ofIndexedOccurrences_recover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexIndexedOccurrenceSplice.lean)
-/
@[path]
private lemma ofIndexedOccurrences_recover_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {n : Nat}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T)
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining source targetPairing n key hinjective) :
-- imply
  (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing n key hinjective hboundary).symm.target = source := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.ofIndexedOccurrences_recover source targetPairing n key hinjective hboundary

/--
[FKColoredStrandSplice.target_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexIndexedOccurrenceSplice.lean)
-/
@[path]
private lemma target_bigrade_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {splice : FKColoredStrandSplice source}
-- given
  (hC : splice.PreservesTotalC) :
-- imply
  (fkColoredLoopPairingPairTotalC splice.target, fkColoredTrueStrandSlotCount splice.target) = (fkColoredLoopPairingPairTotalC source, fkColoredTrueStrandSlotCount source) := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.target_bigrade splice hC


-- created on 2026-10-23
