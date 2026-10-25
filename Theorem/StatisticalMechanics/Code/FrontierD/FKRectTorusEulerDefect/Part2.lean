/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEulerDefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect.Part2
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRandomClusterWeight_critical_eq_loop_defect
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectRandomClusterWeight R (fkRectCriticalP q) q omega =
      fkRectCriticalLoopNormalization R q *
        Real.sqrt q ^ fkRectMedialLoopCount R omega *
          Real.sqrt q ^ fkRectEulerHomologyDefect R omega := by
  rw [fkRectRandomClusterWeight_critical_eq R hq,
    fkRectCriticalReducedWeight_eq_loop_defect R hq]
  unfold fkRectCriticalLoopNormalization
  ring


theorem fkRectRandomClusterWeight_critical_eq_loop_net
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) (s : Nat)
    (hnet : fkRectEulerHomologyDefect R omega = 2 * (s : Int)) :
    fkRectRandomClusterWeight R (fkRectCriticalP q) q omega =
      fkRectCriticalLoopNormalization R q *
        Real.sqrt q ^ fkRectMedialLoopCount R omega * q ^ s := by
  rw [fkRectRandomClusterWeight_critical_eq_loop_defect R hq, hnet]
  have hsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  rw [show (2 * (s : Int)) = (2 * s : Nat) by omega, zpow_natCast]
  rw [pow_mul, Real.sq_sqrt hq.le]

end
end StatMech.FrontierD
