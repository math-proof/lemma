import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedKeySourceRebase.Part2
open StatMech StatMech.FrontierD


/--
[coloredIndexedOccurrenceBoundaryIntertwining_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedKeySourceRebase.lean)
-/
@[path]
private lemma coloredIndexedOccurrenceBoundaryIntertwining_rebase_eq
  {T : EvenTorus}
  {source rebased : FKColoredLoopPairingPair T}
  {n : Nat}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T)
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (hcolor : forall slot : FKLayeredStrandSlot T, fkColoredLayeredSlotColor rebased slot = fkColoredLayeredSlotColor source slot)
  (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining source targetPairing n key hinjective) :
-- imply
  FKColoredIndexedOccurrenceBoundaryIntertwining rebased targetPairing n key hinjective := by
-- proof
  apply StatMech.FrontierD.coloredIndexedOccurrenceBoundaryIntertwining_rebase source rebased targetPairing n key hinjective hcolor hboundary

/--
[indexedOccurrenceSplice_target_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedKeySourceRebase.lean)
-/
@[path]
private lemma indexedOccurrenceSplice_target_rebase_eq
  {T : EvenTorus}
  {source rebased : FKColoredLoopPairingPair T}
  {n : Nat}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T)
  (key : Bool -> Fin n -> T.Vertex × Bool)
  (hinjective : forall layer, Function.Injective (key layer))
  (hcolor : forall slot : FKLayeredStrandSlot T, fkColoredLayeredSlotColor rebased slot = fkColoredLayeredSlotColor source slot)
  (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining source targetPairing n key hinjective) :
-- imply
  (FKColoredStrandSplice.ofIndexedOccurrences rebased targetPairing n key hinjective (coloredIndexedOccurrenceBoundaryIntertwining_rebase source rebased targetPairing n key hinjective hcolor hboundary)).target = (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing n key hinjective hboundary).target := by
-- proof
  apply StatMech.FrontierD.indexedOccurrenceSplice_target_rebase source rebased targetPairing n key hinjective hcolor hboundary

/--
[FKColoredFineTwoCycleUnitTransferRoutedKey.rebase_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedKeySourceRebase.lean)
-/
@[path]
private lemma rebase_target_eq
  {T : EvenTorus}
  {source rebased : FKColoredLoopPairingPair T}
  {certificate : FKColoredFineTwoCycleUnitTransferRoutedKey source}
-- given
  (hcolor : forall slot : FKLayeredStrandSlot T, fkColoredLayeredSlotColor rebased slot = fkColoredLayeredSlotColor source slot)
  (harrows : forall layer, (rebased layer).arrows = (source layer).arrows) :
-- imply
  (certificate.rebase hcolor harrows).splice.target = certificate.splice.target := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferRoutedKey.rebase_target certificate hcolor harrows


-- created on 2026-10-23
