/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedInteractionCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedBoundary.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

@[simp] theorem fkRectRefinedCoverSide_eq (R : FKRectTorus) :
    fkRectSquareCoverSide (fkRectRefinedCoverTorus R) =
      4 * fkRectSquareCoverSide R := by
  simp [fkRectRefinedCoverTorus, fkRectSquareCoverSide, Nat.mul_assoc]

theorem fkRectSquareCoverSide_gt_eight (R : FKRectTorus) :
    8 < fkRectSquareCoverSide R := by
  have hw : 3 <= R.width := R.width_gt_two
  have hh : 3 <= R.height := R.height_gt_two
  calc
    8 < 3 * 3 := by norm_num
    _ <= R.width * R.height := by
      simpa [fkRectSquareCoverSide] using Nat.mul_le_mul hw hh

end
end StatMech.FrontierD
