/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part5


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexLoopFullNegativeMaskOfPreimage
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile)
    (preimage : {source : SixVertexLoopDecoratedPairFineProfileFiber T
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) profile //
      SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
        profile source target}) :
    SixVertexLoopFullNegativeMask profile target := by
  let certificate := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile preimage.1 target preimage.2
  refine ⟨certificate.1, ?_, ?_⟩
  · rw [sixVertexLoopFullUnitMaskOfRelated_false_arrows middle
      hmiddle_pos hmiddle_lt profile preimage.1 target preimage.2,
    sixVertexLoopFullUnitMaskOfRelated_true_arrows middle
      hmiddle_pos hmiddle_lt profile preimage.1 target preimage.2]
    exact certificate.2.1.pairSwitch
  · rw [sixVertexLoopFullUnitMaskOfRelated_false_arrows middle
      hmiddle_pos hmiddle_lt profile preimage.1 target preimage.2,
    sixVertexLoopFullUnitMaskOfRelated_true_arrows middle
      hmiddle_pos hmiddle_lt profile preimage.1 target preimage.2,
    sixVertexTorusMaskSeamTransfer_pairSwitch, certificate.2.2]

end
end StatMech.FrontierD
