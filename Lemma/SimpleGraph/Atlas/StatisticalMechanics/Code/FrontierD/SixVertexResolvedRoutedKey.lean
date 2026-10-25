import Mathlib
import sympy.Basic
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexResolvedRoutedKey
open StatMech StatMech.FrontierD


/--
[FKColoredUnitTransferRoutedKey.splice_preservesTotalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedRoutedKey.lean)
-/
@[path]
private lemma splice_preservesTotalC_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {certificate : FKColoredUnitTransferRoutedKey source} :
-- imply
  certificate.splice.PreservesTotalC := by
-- proof
  apply StatMech.FrontierD.FKColoredUnitTransferRoutedKey.splice_preservesTotalC certificate

/--
[FKColoredUnitTransferRoutedKey.splice_seamDelta_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedRoutedKey.lean)
-/
@[path]
private lemma splice_seamDelta_false_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {certificate : FKColoredUnitTransferRoutedKey source} :
-- imply
  certificate.splice.seamDelta false = 1 := by
-- proof
  apply StatMech.FrontierD.FKColoredUnitTransferRoutedKey.splice_seamDelta_false certificate

/--
[FKColoredUnitTransferRoutedKey.splice_seamDelta_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedRoutedKey.lean)
-/
@[path]
private lemma splice_seamDelta_true_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {certificate : FKColoredUnitTransferRoutedKey source} :
-- imply
  certificate.splice.seamDelta true = -1 := by
-- proof
  apply StatMech.FrontierD.FKColoredUnitTransferRoutedKey.splice_seamDelta_true certificate

/--
[FKColoredUnitTransferRoutedKey.target_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedRoutedKey.lean)
-/
@[path]
private lemma target_bigrade_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {certificate : FKColoredUnitTransferRoutedKey source} :
-- imply
  (fkColoredLoopPairingPairTotalC certificate.splice.target, fkColoredTrueStrandSlotCount certificate.splice.target) = (fkColoredLoopPairingPairTotalC source, fkColoredTrueStrandSlotCount source) := by
-- proof
  apply StatMech.FrontierD.FKColoredUnitTransferRoutedKey.target_bigrade certificate

/--
[FKColoredUnitTransferRoutedKey.recover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedRoutedKey.lean)
-/
@[path]
private lemma recover_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {certificate : FKColoredUnitTransferRoutedKey source} :
-- imply
  certificate.splice.symm.target = source := by
-- proof
  apply StatMech.FrontierD.FKColoredUnitTransferRoutedKey.recover certificate

/--
[FKColoredUnitTransferRoutedKey.target_middleSectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedRoutedKey.lean)
-/
@[path]
private lemma target_middleSectors_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {certificate : FKColoredUnitTransferRoutedKey source}
  {middle : Nat}
-- given
  (hmiddle : 0 < middle)
  (hlower : sixVertexUpCount (svTorusVerticalRows T (source false).arrows (svFinLast T.height_pos)) = middle - 1)
  (hupper : sixVertexUpCount (svTorusVerticalRows T (source true).arrows (svFinLast T.height_pos)) = middle + 1) :
-- imply
  sixVertexUpCount (svTorusVerticalRows T (certificate.splice.target false).arrows (svFinLast T.height_pos)) = middle /\ sixVertexUpCount (svTorusVerticalRows T (certificate.splice.target true).arrows (svFinLast T.height_pos)) = middle := by
-- proof
  apply StatMech.FrontierD.FKColoredUnitTransferRoutedKey.target_middleSectors certificate middle hmiddle hlower hupper


-- created on 2026-10-23
