/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusEulerDefect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusEulerDefect
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCriticalReducedWeight_eq_sqrt_pow
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q omega =
      Real.sqrt q ^
        (fkRectOpenEdgeCount R omega + 2 * fkRectNumClusters R omega) := by
  unfold fkRectCriticalReducedWeight
  calc
    Real.sqrt q ^ fkRectOpenEdgeCount R omega *
        q ^ fkRectNumClusters R omega =
      Real.sqrt q ^ fkRectOpenEdgeCount R omega *
        (Real.sqrt q ^ 2) ^ fkRectNumClusters R omega := by
          rw [Real.sq_sqrt hq.le]
    _ = Real.sqrt q ^ fkRectOpenEdgeCount R omega *
        Real.sqrt q ^ (2 * fkRectNumClusters R omega) := by
          rw [pow_mul]
    _ = Real.sqrt q ^
        (fkRectOpenEdgeCount R omega + 2 * fkRectNumClusters R omega) := by
          rw [pow_add]


theorem fkRectCriticalReducedWeight_eq_loop_defect
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q omega =
      Real.sqrt q ^ (R.width * R.height : Nat) *
        Real.sqrt q ^ fkRectMedialLoopCount R omega *
          Real.sqrt q ^ fkRectEulerHomologyDefect R omega := by
  have hsqrt : Real.sqrt q ≠ 0 := (Real.sqrt_pos.2 hq).ne'
  rw [fkRectCriticalReducedWeight_eq_sqrt_pow R hq]
  rw [<- zpow_natCast]
  rw [show ((fkRectOpenEdgeCount R omega +
      2 * fkRectNumClusters R omega : Nat) : Int) =
      (R.width * R.height : Nat) +
        (fkRectMedialLoopCount R omega : Int) +
          fkRectEulerHomologyDefect R omega by
    unfold fkRectEulerHomologyDefect
    push_cast
    ring]
  rw [zpow_add₀ hsqrt, zpow_add₀ hsqrt]
  simp only [zpow_natCast]


end
end StatMech.FrontierD
