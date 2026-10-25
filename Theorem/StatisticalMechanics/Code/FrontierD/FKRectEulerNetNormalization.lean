/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEulerNetNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEulerNetIdentification
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedSectorNormalization.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRandomClusterWeight_critical_eq_loop_netIndicator
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectRandomClusterWeight R (fkRectCriticalP q) q omega =
      fkRectCriticalLoopNormalization R q *
        Real.sqrt q ^ fkRectMedialLoopCount R omega *
          q ^ fkRectNetIndicator R omega := by
  exact fkRectRandomClusterWeight_critical_eq_loop_net R hq omega
    (fkRectNetIndicator R omega)
    (fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration R omega)


theorem fkRectZeroTurnEulerResidual_eq_netIndicator
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    fkRectZeroTurnEulerResidual R q omega =
      (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
        q ^ fkRectNetIndicator R omega := by
  unfold fkRectZeroTurnEulerResidual
  rw [fkRectEulerHomologyDefect_eq_two_mul_netIndicator_configuration]
  have hq0 : 0 ≤ q := by linarith
  let s := fkRectNetIndicator R omega
  change (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
      Real.sqrt q ^ (2 * (s : Int)) =
    (2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega / q ^ s
  have hs : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
  rw [show 2 * (s : Int) = (2 * s : Nat) by omega, zpow_natCast,
    pow_mul, Real.sq_sqrt hq0]


theorem fkRectAllOrientedLoopTilt_eq_zeroTurn_netIndicator_fkQgt4
    (R : FKRectTorus) {q : Real} (hq : 4 < q)
    (omega : R.Configuration) :
    let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)
    fkRectAllOrientedLoopTilt R q lam omega =
      ((2 / Real.sqrt q) ^ fkRectZeroTurnLoopCount R omega /
          q ^ fkRectNetIndicator R omega) /
        Real.sqrt q ^ (R.width * R.height : Nat) := by
  dsimp only
  rw [fkRectAllOrientedLoopTilt_eq_residual_div_area_fkQgt4 R hq,
    fkRectZeroTurnEulerResidual_eq_netIndicator R hq]


end
end StatMech.FrontierD
