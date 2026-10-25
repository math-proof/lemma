/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part4
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

def fkRectRefinedCoverTorus (R : FKRectTorus) : FKRectTorus where
  width := 4 * R.width
  height := R.height
  width_gt_two := by
    have := R.width_pos
    omega
  height_gt_two := R.height_gt_two
  height_even := R.height_even

end
end StatMech.FrontierD
