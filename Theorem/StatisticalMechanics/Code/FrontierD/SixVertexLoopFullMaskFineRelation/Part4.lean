/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexLoopFullMaskFineRelated_target
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (mask : SixVertexArrows T)
    (hmask : SixVertexFullDisagreementMask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows mask)
    (htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1) :
    SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt profile
      source (sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos
        hmiddle_lt profile source mask hmask htransfer) := by
  exact ⟨mask, hmask, htransfer, rfl⟩


theorem sixVertexLoopDecoratedFullMaskFineTarget_lex
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle
      hmiddle_pos hmiddle_lt source.1) :
    let h := sixVertexLoopDecoratedPositiveSeam middle hmiddle_pos
      hmiddle_lt source.1
    let mask := sixVertexLexDisagreementComponentMask T
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows h
    let hmask := sixVertexLexDisagreementComponentMask_full T
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows h
    sixVertexLoopDecoratedFullMaskFineTarget middle hmiddle_pos hmiddle_lt
        profile source mask hmask hunit =
      sixVertexLoopDecoratedUnitTransferFineTarget middle hmiddle_pos
        hmiddle_lt profile source hunit := by
  dsimp
  rfl

theorem sixVertexLoopLexUnitFineRelated_imp_fullMaskFineRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (hrelated : SixVertexLoopLexUnitFineRelated middle hmiddle_pos
      hmiddle_lt profile source target) :
    SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
      profile source target := by
  obtain ⟨hunit, rfl⟩ := hrelated
  let h := sixVertexLoopDecoratedPositiveSeam middle hmiddle_pos
    hmiddle_lt source.1
  let mask := sixVertexLexDisagreementComponentMask T
    (sixVertexLoopDecoratedPairColored source.1 false).arrows
    (sixVertexLoopDecoratedPairColored source.1 true).arrows h
  let hmask := sixVertexLexDisagreementComponentMask_full T
    (sixVertexLoopDecoratedPairColored source.1 false).arrows
    (sixVertexLoopDecoratedPairColored source.1 true).arrows h
  have htransfer : sixVertexTorusMaskSeamTransfer mask
      (sixVertexLoopDecoratedPairColored source.1 false).arrows
      (sixVertexLoopDecoratedPairColored source.1 true).arrows = 1 := by
    exact hunit
  refine ⟨mask, hmask, htransfer, ?_⟩
  exact (sixVertexLoopDecoratedFullMaskFineTarget_lex middle hmiddle_pos
    hmiddle_lt profile source hunit).symm


end
end StatMech.FrontierD
