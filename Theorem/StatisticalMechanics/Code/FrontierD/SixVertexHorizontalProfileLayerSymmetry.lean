/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexReflectFirstHorizontalLayer_involutive
    {T : EvenTorus} :
    Function.Involutive (sixVertexReflectFirstHorizontalLayer (T := T)) := by
  intro horizontal
  apply Prod.ext
  · funext v
    apply congrArg horizontal.1
    apply Prod.ext
    · exact sixVertexCyclicNeg_involutive T.width_pos v.1
    · rfl
  · rfl

theorem sixVertexReflectSecondHorizontalLayer_involutive
    {T : EvenTorus} :
    Function.Involutive (sixVertexReflectSecondHorizontalLayer (T := T)) := by
  intro horizontal
  apply Prod.ext
  · rfl
  · funext v
    apply congrArg horizontal.2
    apply Prod.ext
    · exact sixVertexCyclicNeg_involutive T.width_pos v.1
    · rfl

theorem sixVertexHorizontalPairBigrade_reflectFirst
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairBigrade
        (sixVertexReflectFirstHorizontalLayer horizontal) =
      sixVertexHorizontalPairBigrade horizontal := by
  unfold sixVertexHorizontalPairBigrade
    sixVertexReflectFirstHorizontalLayer
  rw [sixVertexHorizontalNontransitionCount_reflect,
    sixVertexHorizontalZeroCount_reflect]

theorem sixVertexHorizontalPairBigrade_reflectSecond
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairBigrade
        (sixVertexReflectSecondHorizontalLayer horizontal) =
      sixVertexHorizontalPairBigrade horizontal := by
  unfold sixVertexHorizontalPairBigrade
    sixVertexReflectSecondHorizontalLayer
  rw [sixVertexHorizontalNontransitionCount_reflect,
    sixVertexHorizontalZeroCount_reflect]

end
end StatMech.FrontierD
