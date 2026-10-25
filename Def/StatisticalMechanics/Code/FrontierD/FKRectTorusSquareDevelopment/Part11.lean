/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part11


namespace StatMech.FrontierD

noncomputable section

def FKRectHasSquareLiftNet (R : FKRectTorus)
    (omega : R.Configuration) : Prop :=
  ∃ x : R.Vertex,
    ∃ w z : (fkRectOpenGraph R omega).Walk x x,
      ∃ p q a b : Int × Int,
        FKRectSquareWalkLift R w p q ∧
        FKRectSquareWalkLift R z a b ∧
        FKRectWindingIndependent
          (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p)
          (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a)


end
end StatMech.FrontierD
