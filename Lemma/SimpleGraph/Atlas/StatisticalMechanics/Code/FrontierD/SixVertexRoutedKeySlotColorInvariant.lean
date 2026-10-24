import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySlotColorInvariant
open StatMech StatMech.FrontierD


/--
[FKColoredUnitTransferRoutedKey.ofSlotColorInvariant_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedKeySlotColorInvariant.lean)
-/
@[path]
private lemma ofSlotColorInvariant_splice_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {n : Nat}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T)
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (hinvariant : FKColoredIndexedOccurrenceSlotColorInvariant source targetPairing n key hinjective)
  (hTotalC : (fkColoredSlotColorInvariantSplice source targetPairing n key hinjective hinvariant).PreservesTotalC)
  (hfalse : (fkColoredSlotColorInvariantSplice source targetPairing n key hinjective hinvariant).seamDelta false = 1)
  (htrue : (fkColoredSlotColorInvariantSplice source targetPairing n key hinjective hinvariant).seamDelta true = -1) :
-- imply
  (FKColoredUnitTransferRoutedKey.ofSlotColorInvariant source targetPairing n key hinjective hinvariant hTotalC hfalse htrue).splice = fkColoredSlotColorInvariantSplice source targetPairing n key hinjective hinvariant := by
-- proof
  apply StatMech.FrontierD.FKColoredUnitTransferRoutedKey.ofSlotColorInvariant_splice source targetPairing n key hinjective hinvariant hTotalC hfalse htrue


-- created on 2026-10-23
