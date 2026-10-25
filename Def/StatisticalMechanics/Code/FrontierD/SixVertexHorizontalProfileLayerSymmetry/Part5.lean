/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part4


namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalPairProfileFiberSwapLayersEquiv
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
        sixVertexSwapHorizontalPairCompletionProfile profile} where
  toFun horizontal :=
    ⟨⟨sixVertexSwapHorizontalLayers horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_swapLayers]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_swapLayers, horizontal.2]⟩
  invFun horizontal :=
    ⟨⟨sixVertexSwapHorizontalLayers horizontal.1.1, by
        rw [sixVertexHorizontalPairBigrade_swapLayers]
        exact horizontal.1.2⟩, by
      rw [sixVertexHorizontalPairCompletionProfile_swapLayers, horizontal.2,
        sixVertexSwapHorizontalPairCompletionProfile_involutive]⟩
  left_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexSwapHorizontalLayers_involutive horizontal.1.1
  right_inv horizontal := by
    apply Subtype.ext
    apply Subtype.ext
    exact sixVertexSwapHorizontalLayers_involutive horizontal.1.1

end
end StatMech.FrontierD
