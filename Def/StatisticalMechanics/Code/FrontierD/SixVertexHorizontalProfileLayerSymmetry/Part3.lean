/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part2


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalPairProfileFiberReflectFirstEquiv
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile} ≃
      {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 =
        sixVertexReflectFirstHorizontalPairCompletionProfile profile} where
  toFun horizontal :=
    ⟨⟨sixVertexReflectFirstHorizontalLayer horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflectFirst]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflectFirst, horizontal.2]⟩
  invFun horizontal :=
    ⟨⟨sixVertexReflectFirstHorizontalLayer horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflectFirst]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflectFirst, horizontal.2,
        sixVertexReflectFirstHorizontalPairCompletionProfile_involutive]⟩
  left_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectFirstHorizontalLayer_involutive horizontal.1.1
  right_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectFirstHorizontalLayer_involutive horizontal.1.1

def sixVertexHorizontalPairProfileFiberReflectSecondEquiv
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 = profile} ≃
      {horizontal :
        {horizontal : SixVertexHorizontalField T ×
            SixVertexHorizontalField T //
          sixVertexHorizontalPairBigrade horizontal = grade} //
      sixVertexHorizontalPairCompletionProfile T horizontal.1 =
        sixVertexReflectSecondHorizontalPairCompletionProfile profile} where
  toFun horizontal :=
    ⟨⟨sixVertexReflectSecondHorizontalLayer horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflectSecond]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflectSecond, horizontal.2]⟩
  invFun horizontal :=
    ⟨⟨sixVertexReflectSecondHorizontalLayer horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflectSecond]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflectSecond, horizontal.2,
        sixVertexReflectSecondHorizontalPairCompletionProfile_involutive]⟩
  left_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectSecondHorizontalLayer_involutive horizontal.1.1
  right_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectSecondHorizontalLayer_involutive horizontal.1.1

end
end StatMech.FrontierD
