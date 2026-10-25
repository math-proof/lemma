/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedWalkCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSquareCoverDartList
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedWalkCarrier


namespace StatMech.FrontierD

noncomputable section

theorem FKRectRefinedWalkCarrier.path_translation
    {R : FKRectTorus} {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    {h : FKRectSquareWalkLift R w p q}
    (C : FKRectRefinedWalkCarrier R h) :
    FKRectIntegralSquareDartPath
      (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))
      ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 +
          C.translation.1,
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 +
          C.translation.2)
      C.darts := by
  have hend : fkRectRefinedScalePoint (fkRectSquareDevelopPoint q) =
      ((fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).1 +
          C.translation.1,
        (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)).2 +
          C.translation.2) := by
    apply Prod.ext <;>
      simp [FKRectRefinedWalkCarrier.translation,
        fkRectRefinedScalePoint] <;> ring
  rw [← hend]
  exact C.path


end
end StatMech.FrontierD
