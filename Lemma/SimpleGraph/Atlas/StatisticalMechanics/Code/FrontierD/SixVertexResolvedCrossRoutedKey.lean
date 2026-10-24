import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexResolvedCrossRoutedKey
open StatMech StatMech.FrontierD


/--
[fkColoredVertexCrossOccurrenceKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean)
-/
@[path]
private lemma fkColoredVertexCrossOccurrenceKey_injective_eq
  {T : EvenTorus}
  {layer : Bool}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  Function.Injective (fkColoredVertexCrossOccurrenceKey mask layer) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossOccurrenceKey_injective mask layer

/--
[fkColoredVertexCrossOccurrenceKey_exists_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean)
-/
@[path]
private lemma fkColoredVertexCrossOccurrenceKey_exists_iff_eq
  {T : EvenTorus}
  {layer : Bool}
  {slot : T.Vertex × Bool}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  (exists i, fkColoredVertexCrossOccurrenceKey mask layer i = slot) ↔ mask slot.1 = true := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossOccurrenceKey_exists_iff mask layer slot

/--
[fkIndexedOccurrenceSlotEquiv_vertexCross_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean)
-/
@[path]
private lemma fkIndexedOccurrenceSlotEquiv_vertexCross_eq_eq
  {T : EvenTorus}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  fkIndexedOccurrenceSlotEquiv (Fintype.card (FKColoredVertexCrossOccurrence mask)) (fkColoredVertexCrossOccurrenceKey mask) (fkColoredVertexCrossOccurrenceKey_injective mask) = fkColoredFullSwapLayeredSlotEquiv mask := by
-- proof
  apply StatMech.FrontierD.fkIndexedOccurrenceSlotEquiv_vertexCross_eq mask

/--
[fkColoredVertexCrossTarget_slotColorEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_slotColorEquiv_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {cross : FKColoredResolvedUnitCross source} :
-- imply
  FKColoredStrandSlotColorEquiv source cross.target (fkColoredFullSwapLayeredSlotEquiv cross.mask) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_slotColorEquiv source cross

/--
[FKColoredResolvedUnitCross.boundaryIntertwining](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean)
-/
@[path]
private lemma boundaryIntertwining_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {cross : FKColoredResolvedUnitCross source} :
-- imply
  FKColoredIndexedOccurrenceBoundaryIntertwining source (fun layer => (source layer).pairing) (Fintype.card (FKColoredVertexCrossOccurrence cross.mask)) (fkColoredVertexCrossOccurrenceKey cross.mask) (fkColoredVertexCrossOccurrenceKey_injective cross.mask) := by
-- proof
  apply StatMech.FrontierD.FKColoredResolvedUnitCross.boundaryIntertwining cross

/--
[FKColoredResolvedUnitCross.indexedSplice_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedCrossRoutedKey.lean)
-/
@[path]
private lemma indexedSplice_target_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {cross : FKColoredResolvedUnitCross source} :
-- imply
  (FKColoredStrandSplice.ofIndexedOccurrences source (fun layer => (source layer).pairing) (Fintype.card (FKColoredVertexCrossOccurrence cross.mask)) (fkColoredVertexCrossOccurrenceKey cross.mask) (fkColoredVertexCrossOccurrenceKey_injective cross.mask) cross.boundaryIntertwining).target = cross.target := by
-- proof
  apply StatMech.FrontierD.FKColoredResolvedUnitCross.indexedSplice_target cross


-- created on 2026-10-23
