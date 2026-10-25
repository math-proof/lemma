/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectWalkWinding_copy (R : FKRectTorus)
    {G : SimpleGraph R.Vertex} {u v u' v' : R.Vertex}
    (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    fkRectWalkWinding R (p.copy hu hv) = fkRectWalkWinding R p := by
  subst u'
  subst v'
  rfl

theorem fkRectHorizontalFundamentalWalk_winding (R : FKRectTorus) :
    fkRectWalkWinding R (fkRectHorizontalFundamentalWalk R) = (-1, 0) := by
  unfold fkRectHorizontalFundamentalWalk
  rw [fkRectWalkWinding_copy]
  rw [fkRectHorizontalFundamentalWalkAux_winding R R.width (le_refl _)]
  simp [ne_of_gt R.width_pos]

theorem fkRectVerticalFundamentalWalk_winding (R : FKRectTorus) :
    fkRectWalkWinding R (fkRectVerticalFundamentalWalk R) = (0, -1) := by
  unfold fkRectVerticalFundamentalWalk
  rw [fkRectWalkWinding_copy]
  rw [fkRectVerticalFundamentalWalkAux_winding R _ R.height (le_refl _)]
  simp [ne_of_gt R.height_pos]

theorem FKRectHasNet_univ (R : FKRectTorus) :
    FKRectHasNet R (fkRectConfigurationOfEdges R Finset.univ) := by
  refine ⟨fkRectOrigin R, fkRectHorizontalFundamentalWalk R,
    fkRectVerticalFundamentalWalk R, ?_⟩
  rw [fkRectHorizontalFundamentalWalk_winding,
    fkRectVerticalFundamentalWalk_winding]
  norm_num [FKRectWindingIndependent]

@[simp] theorem fkRectNetIndicator_univ (R : FKRectTorus) :
    fkRectNetIndicator R (fkRectConfigurationOfEdges R Finset.univ) = 1 :=
  (fkRectNetIndicator_eq_one_iff R _).2 (FKRectHasNet_univ R)

end
end StatMech.FrontierD
