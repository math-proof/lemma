/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileLayerSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9


namespace StatMech.FrontierD

noncomputable section

def sixVertexReflectFirstHorizontalLayer
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  (sixVertexReflectHorizontalField horizontal.1, horizontal.2)

def sixVertexReflectSecondHorizontalLayer
    {T : EvenTorus}
    (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
    SixVertexHorizontalField T × SixVertexHorizontalField T :=
  (horizontal.1, sixVertexReflectHorizontalField horizontal.2)

end
end StatMech.FrontierD
