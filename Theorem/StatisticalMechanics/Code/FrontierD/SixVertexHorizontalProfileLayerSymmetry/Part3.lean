/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part3


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexHorizontalPairProfileMultiplicity_reflectFirst
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalPairProfileMultiplicity T grade
        (sixVertexReflectFirstHorizontalPairCompletionProfile profile) =
      sixVertexHorizontalPairProfileMultiplicity T grade profile := by
  unfold sixVertexHorizontalPairProfileMultiplicity
  exact Fintype.card_congr
    (sixVertexHorizontalPairProfileFiberReflectFirstEquiv T grade profile).symm

theorem sixVertexHorizontalPairProfileMultiplicity_reflectSecond
    (T : EvenTorus) (grade : Nat × Nat)
    (profile : SixVertexHorizontalPairCompletionProfile T) :
    sixVertexHorizontalPairProfileMultiplicity T grade
        (sixVertexReflectSecondHorizontalPairCompletionProfile profile) =
      sixVertexHorizontalPairProfileMultiplicity T grade profile := by
  unfold sixVertexHorizontalPairProfileMultiplicity
  exact Fintype.card_congr
    (sixVertexHorizontalPairProfileFiberReflectSecondEquiv T grade profile).symm

end
end StatMech.FrontierD
