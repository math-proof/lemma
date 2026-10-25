/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileSign
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexReflectHorizontalField
    {T : EvenTorus} (horizontal : SixVertexHorizontalField T) :
    SixVertexHorizontalField T :=
  fun v => horizontal (sixVertexCyclicNeg T.width_pos v.1, v.2)

end
end StatMech.FrontierD
