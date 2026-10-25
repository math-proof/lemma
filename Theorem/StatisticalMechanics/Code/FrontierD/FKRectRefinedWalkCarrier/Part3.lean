/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedWalkCarrier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSquareCoverDartList
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedWalkCarrier.Part2


namespace StatMech.FrontierD

noncomputable section

theorem FKRectRefinedWalkCarrier.interaction_ne_zero_iff_windingIndependent
    (R : FKRectTorus)
    {G H : SimpleGraph R.Vertex} {x y : R.Vertex}
    {w : G.Walk x x} {z : H.Walk y y}
    {p q a b : Int × Int}
    {hw : FKRectSquareWalkLift R w p q}
    {hz : FKRectSquareWalkLift R z a b}
    (C : FKRectRefinedWalkCarrier R hw)
    (D : FKRectRefinedWalkCarrier R hz) :
    fkRectRefinedRawInteraction C.coverDarts D.coverDarts ≠ 0 ↔
      FKRectWindingIndependent
        (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
  change fkRectRefinedRawInteraction
      (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
        C.darts C.translation)
      (fkRectSquareCoverDartList (fkRectRefinedCoverTorus R)
        D.darts D.translation) ≠ 0 ↔ _
  rw [fkRectSquareCoverDartList_interaction_ne_zero_iff
    (fkRectRefinedCoverTorus R) C.path_translation D.path_translation]
  change FKRectWindingIndependent
      (4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).1,
        4 * (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p).2)
      (4 * (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a).1,
        4 * (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a).2) ↔ _
  rw [fkRectWindingIndependent_four_iff]
  exact hw.closed_developedIndependent_iff R hz

end
end StatMech.FrontierD
