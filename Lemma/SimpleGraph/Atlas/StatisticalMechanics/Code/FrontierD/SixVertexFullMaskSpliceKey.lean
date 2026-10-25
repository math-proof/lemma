import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullMaskSpliceKey.Part2
open StatMech StatMech.FrontierD


/--
[sixVertexFullUnitMaskSplice_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullMaskSpliceKey.lean)
-/
@[path]
private lemma sixVertexFullUnitMaskSplice_target_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask (source false).arrows (source true).arrows mask) :
-- imply
  (sixVertexFullUnitMaskSplice source mask hmask).target = sixVertexFullDisagreementColoredTarget source mask hmask := by
-- proof
  apply StatMech.FrontierD.sixVertexFullUnitMaskSplice_target source mask hmask

/--
[sixVertexFullUnitMaskSplice_preservesTotalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullMaskSpliceKey.lean)
-/
@[path]
private lemma sixVertexFullUnitMaskSplice_preservesTotalC_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask (source false).arrows (source true).arrows mask) :
-- imply
  (sixVertexFullUnitMaskSplice source mask hmask).PreservesTotalC := by
-- proof
  apply StatMech.FrontierD.sixVertexFullUnitMaskSplice_preservesTotalC source mask hmask

/--
[sixVertexFullUnitMaskSplice_seamDelta_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullMaskSpliceKey.lean)
-/
@[path]
private lemma sixVertexFullUnitMaskSplice_seamDelta_false_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask (source false).arrows (source true).arrows mask)
  (htransfer : sixVertexTorusMaskSeamTransfer mask (source false).arrows (source true).arrows = 1) :
-- imply
  (sixVertexFullUnitMaskSplice source mask hmask).seamDelta false = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFullUnitMaskSplice_seamDelta_false source mask hmask htransfer

/--
[sixVertexFullUnitMaskSplice_seamDelta_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullMaskSpliceKey.lean)
-/
@[path]
private lemma sixVertexFullUnitMaskSplice_seamDelta_true_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask (source false).arrows (source true).arrows mask)
  (htransfer : sixVertexTorusMaskSeamTransfer mask (source false).arrows (source true).arrows = 1) :
-- imply
  (sixVertexFullUnitMaskSplice source mask hmask).seamDelta true = -1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFullUnitMaskSplice_seamDelta_true source mask hmask htransfer

/--
[sixVertexFullUnitMaskSpliceKey_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullMaskSpliceKey.lean)
-/
@[path]
private lemma sixVertexFullUnitMaskSpliceKey_target_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask (source false).arrows (source true).arrows mask)
  (htransfer : sixVertexTorusMaskSeamTransfer mask (source false).arrows (source true).arrows = 1) :
-- imply
  (sixVertexFullUnitMaskSpliceKey source mask hmask htransfer).splice.target = sixVertexFullDisagreementColoredTarget source mask hmask := by
-- proof
  apply StatMech.FrontierD.sixVertexFullUnitMaskSpliceKey_target source mask hmask htransfer


-- created on 2026-10-23
