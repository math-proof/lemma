/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusDevelopedWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingSubgroup.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectWalkDevelopedDisplacement (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} {x y : R.Vertex} :
    G.Walk x y -> Int × Int
  | .nil' _ => 0
  | .cons' x z _ _ p =>
      fkRectDevelopedStep R x z +
        fkRectWalkDevelopedDisplacement R p


end
end StatMech.FrontierD
