/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleDuality
open Equiv SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectDualBlackDartEquiv
    (R : FKRectTorus) (omega : R.Configuration) :
    FKMedialBlackDart R.medialTorus ≃ FKMedialBlackDart R.medialTorus where
  toFun d := ⟨fkMedialLocalMate
      (fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega))
      (fkRectMedialDualShiftDart R d.1), by
    rw [fkMedialCheckerColor_localMate_eq_not,
      fkMedialCheckerColor_dualShift, d.2]
    rfl⟩
  invFun d := ⟨fkRectMedialDualUnshiftDart R
      (fkMedialLocalMate
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega)) d.1), by
    rw [fkMedialCheckerColor_dualUnshift,
      fkMedialCheckerColor_localMate_eq_not, d.2]
    rfl⟩
  left_inv d := by
    apply Subtype.ext
    simp only [fkMedialLocalMate_involutive,
      fkRectMedialDualUnshiftDart_shift]
  right_inv d := by
    apply Subtype.ext
    simp only [fkRectMedialDualShiftDart_unshift,
      fkMedialLocalMate_involutive]


end
end StatMech.FrontierD
