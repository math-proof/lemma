/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalResidualCompletions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalActualDeficitSupport.Part3
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalProfileDeficit_eq_sub
    {T : EvenTorus}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalProfileDeficit
        sourceLeft sourceRight targetLeft targetRight profile =
      sixVertexHorizontalPairProfileChooseWeight
          sourceLeft sourceRight profile -
        sixVertexHorizontalPairProfileChooseWeight
          targetLeft targetRight profile := by
  unfold sixVertexHorizontalProfileDeficit
    sixVertexHorizontalProfileSignedKernel
  omega

theorem sixVertexHorizontalProfileSurplus_eq_sub
    {T : EvenTorus}
    (sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1))
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalProfileSurplus
        sourceLeft sourceRight targetLeft targetRight profile =
      sixVertexHorizontalPairProfileChooseWeight
          targetLeft targetRight profile -
        sixVertexHorizontalPairProfileChooseWeight
          sourceLeft sourceRight profile := by
  unfold sixVertexHorizontalProfileSurplus
    sixVertexHorizontalProfileSignedKernel
  omega


theorem sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_left_isEmpty
    {T : EvenTorus} (sourceLeft sourceRight : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (hleft : IsEmpty
      (SixVertexHorizontalSectorCompletion T sourceLeft horizontal.1)) :
    sixVertexHorizontalPairProfileChooseWeight sourceLeft sourceRight
        (sixVertexHorizontalPairCompletionProfile T horizontal) = 0 := by
  rw [← sixVertexHorizontalPairChooseWeight_eq_profile]
  rw [sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty
    T sourceLeft horizontal.1 hleft, zero_mul]


theorem sixVertexHorizontalPairProfileChooseWeight_eq_zero_of_right_isEmpty
    {T : EvenTorus} (sourceLeft sourceRight : Fin (T.width + 1))
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T)
    (hright : IsEmpty
      (SixVertexHorizontalSectorCompletion T sourceRight horizontal.2)) :
    sixVertexHorizontalPairProfileChooseWeight sourceLeft sourceRight
        (sixVertexHorizontalPairCompletionProfile T horizontal) = 0 := by
  rw [← sixVertexHorizontalPairChooseWeight_eq_profile]
  rw [sixVertexHorizontalSectorCompletionChooseCount_eq_zero_of_isEmpty
    T sourceRight horizontal.2 hright, mul_zero]


end
end StatMech.FrontierD
