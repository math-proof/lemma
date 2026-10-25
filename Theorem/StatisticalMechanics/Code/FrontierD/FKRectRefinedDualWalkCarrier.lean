/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedDualWalkCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualOpenWalkCarrier
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedWalkCarrier.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedDualWalkCarrier


namespace StatMech.FrontierD

noncomputable section

theorem FKRectRefinedDualWalkCarrier.path_translation
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (D : FKRectRefinedDualWalkCarrier R h) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p))
      ((fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).1 +
          D.translation.1,
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).2 +
          D.translation.2)
      D.darts := by
  have hend : fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint q) =
      ((fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).1 +
          D.translation.1,
        (fkRectRefinedDualScalePoint (fkRectSquareDevelopPoint p)).2 +
          D.translation.2) := by
    apply Prod.ext <;>
      simp [FKRectRefinedDualWalkCarrier.translation,
        fkRectRefinedDualScalePoint] <;> ring
  rw [← hend]
  exact D.path


end
end StatMech.FrontierD
