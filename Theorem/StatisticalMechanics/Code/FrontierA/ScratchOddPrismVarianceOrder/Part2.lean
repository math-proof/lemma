/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ScratchOddPrismVarianceOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismAgreementKernelCauchy
import Instance.StatisticalMechanics.Code.FrontierA.ScratchOddPrismVarianceOrder


namespace StatMech.FrontierA

open StatMech StatMech.Ising

open scoped BigOperators

noncomputable section

theorem oddPrismUnequalBridgeVariance_zero (beta r : Real) :
    unequalReplicaBridgeVariance
        (oddPrismLowerBlockGraph 0) (oddPrismUpperBlockGraph 0)
        (oddPrismUnequalGlueGraph 0) beta
        (fun v => beta * oddPrismPlusField 0 v.1)
        (fun v => beta * oddPrismPlusField 0 v.1) r = 0 := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph 0).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph 0).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph 0).Adj := Classical.decRel _
  exact unequalReplicaBridgeVariance_eq_zero_of_isEmpty_right
    (oddPrismLowerBlockGraph 0) (oddPrismUpperBlockGraph 0)
    (oddPrismUnequalGlueGraph 0)
    (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph 0)
      (oddPrismAtOrBelowCenter 0)) beta _ _ r

theorem oddPrismUnequalBridgeVarianceOrder_zero (beta : Real) :
    OddPrismUnequalBridgeVarianceOrder beta 0 := by
  intro t _
  rw [oddPrismUnequalBridgeVariance_zero beta t,
    oddPrismUnequalBridgeVariance_zero beta (-t)]

theorem oddPrismUnequalBridgeVarianceOrder_iff_transfer
    (beta : Real) (n : Nat) (hn : 0 < n) :
    OddPrismUnequalBridgeVarianceOrder beta n ↔
      ∀ t, 0 <= t ->
        oddPrismTransferBridgeVariance beta n t <=
          oddPrismTransferBridgeVariance beta n (-t) := by
  unfold OddPrismUnequalBridgeVarianceOrder
  simp_rw [oddPrismUnequalBridgeVariance_eq_transfer beta n hn]

end
end StatMech.FrontierA
