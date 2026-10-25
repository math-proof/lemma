/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalTwoCutSwitch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalPairSwitch.Part4
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalTwoCutSwitch.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalTwoCutMask_boundaryBalanced
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    {a b : Fin T.width} (hab : a.val < b.val)
    (hbalanced : SixVertexHorizontalPairTwoCutBalanced horizontal a b) :
    SixVertexHorizontalPairSwitchBoundaryBalanced
      (sixVertexHorizontalTwoCutMask a b) horizontal := by
  unfold SixVertexHorizontalPairSwitchBoundaryBalanced
  rw [sixVertexHorizontalTwoCutMask_sum_boundary hab,
    sixVertexHorizontalTwoCutMask_sum_boundary hab]
  simpa [SixVertexHorizontalPairTwoCutBalanced,
    sixVertexHorizontalPairColumnCrossAgreementCount,
    sixVertexHorizontalPairColumnAgreementCount] using hbalanced


theorem sixVertexHorizontalTwoCutSwitch_bigrade
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    {a b : Fin T.width} (hab : a.val < b.val)
    (hbalanced : SixVertexHorizontalPairTwoCutBalanced horizontal a b) :
    sixVertexHorizontalPairBigrade
        (sixVertexSwitchHorizontalPair
          (sixVertexHorizontalTwoCutMask a b) horizontal) =
      sixVertexHorizontalPairBigrade horizontal :=
  sixVertexSwitchHorizontalPair_bigrade_of_boundaryBalanced _ _
    (sixVertexHorizontalTwoCutMask_boundaryBalanced horizontal hab hbalanced)

end
end StatMech.FrontierD
