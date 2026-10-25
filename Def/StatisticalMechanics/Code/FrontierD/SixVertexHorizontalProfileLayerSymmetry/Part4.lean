/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileLayerSymmetry.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexSwapHorizontalLayers
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  (horizontal.2, horizontal.1)

def sixVertexSwapHorizontalPairCompletionProfile
    {T : EvenTorus} (profile : SixVertexHorizontalPairCompletionProfile T) :
    SixVertexHorizontalPairCompletionProfile T :=
  (profile.2, profile.1)

end
end StatMech.FrontierD
