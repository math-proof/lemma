/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexReflectHorizontalCompletionProfile
    {T : EvenTorus} (profile : SixVertexHorizontalCompletionProfile T) :
    SixVertexHorizontalCompletionProfile T where
  forcedTrue :=
    if hvalid : profile.forcedTrue.val + profile.free.val <= T.width then
      ⟨T.width - profile.free.val - profile.forcedTrue.val,
        Nat.lt_succ_of_le (by omega)⟩
    else profile.forcedTrue
  free := profile.free

end
end StatMech.FrontierD
