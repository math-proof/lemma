/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part2


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexReflectFirstHorizontalPairCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexReflectFirstHorizontalPairCompletionProfile (T := T)) := by
  intro profile
  apply Prod.ext
  · exact sixVertexReflectOptionalHorizontalCompletionProfile_involutive
      profile.1
  · rfl

theorem sixVertexReflectSecondHorizontalPairCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexReflectSecondHorizontalPairCompletionProfile (T := T)) := by
  intro profile
  apply Prod.ext
  · rfl
  · exact sixVertexReflectOptionalHorizontalCompletionProfile_involutive
      profile.2

theorem sixVertexHorizontalPairCompletionProfile_reflectFirst
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairCompletionProfile T
        (sixVertexReflectFirstHorizontalLayer horizontal) =
      sixVertexReflectFirstHorizontalPairCompletionProfile
        (sixVertexHorizontalPairCompletionProfile T horizontal) := by
  apply Prod.ext
  · exact sixVertexHorizontalCompletionProfile_reflect horizontal.1
  · rfl

theorem sixVertexHorizontalPairCompletionProfile_reflectSecond
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairCompletionProfile T
        (sixVertexReflectSecondHorizontalLayer horizontal) =
      sixVertexReflectSecondHorizontalPairCompletionProfile
        (sixVertexHorizontalPairCompletionProfile T horizontal) := by
  apply Prod.ext
  · rfl
  · exact sixVertexHorizontalCompletionProfile_reflect horizontal.2

end
end StatMech.FrontierD
