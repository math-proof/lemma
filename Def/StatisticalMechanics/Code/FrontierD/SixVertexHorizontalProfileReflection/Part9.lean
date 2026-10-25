/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalPairProfileFiberReflectEquiv
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
        sixVertexReflectHorizontalPairCompletionProfile profile} where
  toFun horizontal :=
    ⟨⟨sixVertexReflectHorizontalPair horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflect]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflect, horizontal.2]⟩
  invFun horizontal :=
    ⟨⟨sixVertexReflectHorizontalPair horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_reflect]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_reflect, horizontal.2,
        sixVertexReflectHorizontalPairCompletionProfile_involutive]⟩
  left_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectHorizontalPair_involutive horizontal.1.1
  right_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexReflectHorizontalPair_involutive horizontal.1.1

end
end StatMech.FrontierD
