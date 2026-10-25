/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part4


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSwapHorizontalLayers_involutive
    {T : EvenTorus} :
    Function.Involutive (sixVertexSwapHorizontalLayers (T := T)) := by
  intro horizontal
  rfl

theorem sixVertexSwapHorizontalPairCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexSwapHorizontalPairCompletionProfile (T := T)) := by
  intro profile
  rfl

theorem sixVertexHorizontalPairBigrade_swapLayers
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairBigrade
        (sixVertexSwapHorizontalLayers horizontal) =
      sixVertexHorizontalPairBigrade horizontal := by
  unfold sixVertexHorizontalPairBigrade sixVertexSwapHorizontalLayers
  simp only [add_comm]

theorem sixVertexHorizontalPairCompletionProfile_swapLayers
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairCompletionProfile T
        (sixVertexSwapHorizontalLayers horizontal) =
      sixVertexSwapHorizontalPairCompletionProfile
        (sixVertexHorizontalPairCompletionProfile T horizontal) := by
  rfl

end
end StatMech.FrontierD
