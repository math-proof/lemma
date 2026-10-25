/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalPairProfileMultiplicity_reflect
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalPairProfileMultiplicity T grade
        (sixVertexReflectHorizontalPairCompletionProfile profile) =
      sixVertexHorizontalPairProfileMultiplicity T grade profile := by
  unfold sixVertexHorizontalPairProfileMultiplicity
  exact Fintype.card_congr
    (sixVertexHorizontalPairProfileFiberReflectEquiv T grade profile).symm

end
end StatMech.FrontierD
