/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareCoverIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FrontierD.IntegralSquareTorusIntersection.Part9
import Inductive.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareCoverIntersection
open scoped BigOperators


namespace StatMech.FrontierD

open StatMech.Onsager

noncomputable section

theorem FKRectSquareWalkLift.exists_integralDartPath
    (R : FKRectTorus) {G : SimpleGraph R.Vertex}
    {x y : R.Vertex} {w : G.Walk x y} {p q : Int × Int}
    (h : FKRectSquareWalkLift R w p q) :
    ∃ l : List FKRectIntegralSquareDart,
      FKRectIntegralSquareDartPath
        (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) l ∧
      l.length = w.darts.length := by
  induction h with
  | nil p hp =>
      exact ⟨[], FKRectIntegralSquareDartPath.nil _, by simp⟩
  | @cons x y z hxy w p q r hp hq hdisp haxis tail ih =>
      obtain ⟨l, hl, hlen⟩ := ih
      obtain ⟨mu, hmu⟩ := haxis.exists_direction
      refine ⟨((fkRectSquareDevelopPoint p, mu) :: l),
        FKRectIntegralSquareDartPath.cons _ hmu hl, ?_⟩
      simp [hlen]


end
end StatMech.FrontierD
