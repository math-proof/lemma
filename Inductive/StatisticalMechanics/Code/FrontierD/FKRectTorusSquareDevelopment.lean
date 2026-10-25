/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part9


namespace StatMech.FrontierD

noncomputable section

inductive FKRectSquareWalkLift (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} :
    {x y : R.Vertex} → G.Walk x y →
      (Int × Int) → (Int × Int) → Prop
  | nil {x : R.Vertex} (p : Int × Int)
      (hp : fkRectLiftedVertex R p = x) :
      FKRectSquareWalkLift R (.nil : G.Walk x x) p p
  | cons {x y z : R.Vertex} {hxy : G.Adj x y}
      {w : G.Walk y z} {p q r : Int × Int}
      (hp : fkRectLiftedVertex R p = x)
      (hq : fkRectLiftedVertex R q = y)
      (hdisp : q - p = fkRectDevelopedStep R x y)
      (haxis : FKRectSquareAxisStep (fkRectSquareDevelopPoint p)
        (fkRectSquareDevelopPoint q))
      (tail : FKRectSquareWalkLift R w q r) :
      FKRectSquareWalkLift R (.cons hxy w) p r


end
end StatMech.FrontierD
