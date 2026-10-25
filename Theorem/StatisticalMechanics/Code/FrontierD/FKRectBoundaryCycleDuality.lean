/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part8
open Equiv SimpleGraph


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkMedialCheckerColor_dualShift
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkMedialCheckerColor (fkRectMedialDualShiftDart R d) =
      !fkMedialCheckerColor d := by
  rcases d with ⟨⟨i, j⟩, side⟩
  cases side <;>
    simp [fkRectMedialDualShiftDart, fkRectMedialDualShiftVertex,
      fkMedialCheckerColor, fkMedialSideVertical]


@[simp] theorem fkMedialCheckerColor_dualUnshift
    (R : FKRectTorus) (d : FKMedialDart R.medialTorus) :
    fkMedialCheckerColor (fkRectMedialDualUnshiftDart R d) =
      !fkMedialCheckerColor d := by
  have h := fkMedialCheckerColor_dualShift R
    (fkRectMedialDualUnshiftDart R d)
  rw [fkRectMedialDualShiftDart_unshift] at h
  cases hc : fkMedialCheckerColor d <;> simp_all


end
end StatMech.FrontierD
