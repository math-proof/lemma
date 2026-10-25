/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part6
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalCompletionProfile_ext
    {T : EvenTorus} {first second : SixVertexHorizontalCompletionProfile T}
    (hforced : first.forcedTrue = second.forcedTrue)
    (hfree : first.free = second.free) : first = second := by
  cases first
  cases second
  simp_all

theorem sixVertexReflectHorizontalCompletionProfile_involutive
    {T : EvenTorus} :
    Function.Involutive
      (sixVertexReflectHorizontalCompletionProfile (T := T)) := by
  intro profile
  apply sixVertexHorizontalCompletionProfile_ext
  · apply Fin.ext
    by_cases hvalid :
        profile.forcedTrue.val + profile.free.val <= T.width
    · have hreflectedValid :
          (T.width - profile.free.val - profile.forcedTrue.val) +
              profile.free.val <= T.width := by omega
      simp [sixVertexReflectHorizontalCompletionProfile, hvalid,
        hreflectedValid]
      omega
    · simp [sixVertexReflectHorizontalCompletionProfile, hvalid]
  · rfl

end
end StatMech.FrontierD
