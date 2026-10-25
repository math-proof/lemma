/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexReflectHorizontalPairCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexReflectHorizontalPairCompletionProfile (T := T)) := by
  intro profile
  apply Prod.ext
  · exact sixVertexReflectOptionalHorizontalCompletionProfile_involutive
      profile.1
  · exact sixVertexReflectOptionalHorizontalCompletionProfile_involutive
      profile.2

theorem sixVertexHorizontalPairCompletionProfile_reflect
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    sixVertexHorizontalPairCompletionProfile T
        (sixVertexReflectHorizontalPair horizontal) =
      sixVertexReflectHorizontalPairCompletionProfile
        (sixVertexHorizontalPairCompletionProfile T horizontal) := by
  apply Prod.ext
  · exact sixVertexHorizontalCompletionProfile_reflect horizontal.1
  · exact sixVertexHorizontalCompletionProfile_reflect horizontal.2

end
end StatMech.FrontierD
