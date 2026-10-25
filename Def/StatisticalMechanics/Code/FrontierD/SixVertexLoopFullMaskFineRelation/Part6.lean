/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFullMaskFineRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFullMaskFineRelation.Part6


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexLoopFullUnitMaskEquivRelated
    {T : EvenTorus} (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (profile : SixVertexHorizontalBoundedFineRowProfile T)
    (source : SixVertexLoopDecoratedPairFineProfileFiber T
      (sixVertexHorizontalLowerSector middle hmiddle_pos)
      (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) :
    SixVertexLoopFullUnitMask middle hmiddle_pos hmiddle_lt profile source ≃
      {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile //
        SixVertexLoopFullMaskFineRelated middle hmiddle_pos hmiddle_lt
          profile source target} where
  toFun certificate := ⟨sixVertexLoopFullUnitMaskTarget middle hmiddle_pos
    hmiddle_lt profile source certificate,
    sixVertexLoopFullMaskFineRelated_target middle hmiddle_pos hmiddle_lt
      profile source certificate.1 certificate.2.1 certificate.2.2⟩
  invFun target := sixVertexLoopFullUnitMaskOfRelated middle hmiddle_pos
    hmiddle_lt profile source target.1 target.2
  left_inv certificate := by
    apply sixVertexLoopFullUnitMaskTarget_injective middle hmiddle_pos
      hmiddle_lt profile source
    exact (sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos
      hmiddle_lt profile source _ _).symm
  right_inv target := by
    apply Subtype.ext
    exact (sixVertexLoopFullUnitMaskOfRelated_target middle hmiddle_pos
      hmiddle_lt profile source target.1 target.2).symm

end
end StatMech.FrontierD
