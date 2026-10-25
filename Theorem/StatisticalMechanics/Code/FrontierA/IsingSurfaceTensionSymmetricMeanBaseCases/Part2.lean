/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanBaseCases.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCriticalSymmetricMean.Part2
import Instance.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanBaseCases


namespace StatMech.FrontierA

open StatMech StatMech.Ising

noncomputable section

theorem oddPrismUnequalBridgeMean_zero_prism (beta r : Real) :
    unequalReplicaBridgeMean
        (oddPrismLowerBlockGraph 0) (oddPrismUpperBlockGraph 0)
        (oddPrismUnequalGlueGraph 0) beta
        (fun v => beta * oddPrismPlusField 0 v.1)
        (fun v => beta * oddPrismPlusField 0 v.1) r = 0 := by
  classical
  letI : DecidableRel (oddPrismLowerBlockGraph 0).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUpperBlockGraph 0).Adj := Classical.decRel _
  letI : DecidableRel (oddPrismUnequalGlueGraph 0).Adj := Classical.decRel _
  exact unequalReplicaBridgeMean_eq_zero_of_right_empty
    (oddPrismLowerBlockGraph 0) (oddPrismUpperBlockGraph 0)
    (oddPrismUnequalGlueGraph 0)
    (StatMech.FK.agl_partitionCrossInterface (oddPrismInternalGraph 0)
      (oddPrismAtOrBelowCenter 0)) beta _ _ r


theorem oddPrismUnequalBridgeSymmetricMeanOrder_zero_prism (beta : Real) :
    OddPrismUnequalBridgeSymmetricMeanOrder beta 0 := by
  intro t _ _
  rw [oddPrismUnequalBridgeMean_zero_prism beta t,
    oddPrismUnequalBridgeMean_zero_prism beta (-t),
    oddPrismUnequalBridgeMean_zero_prism beta 0]
  norm_num


theorem oddPrismUnequalBridgeSymmetricMeanOrder_zero_coupling (n : Nat) :
    OddPrismUnequalBridgeSymmetricMeanOrder 0 n := by
  intro t ht0 ht1
  have ht : t = 0 := le_antisymm ht1 ht0
  subst t
  simp only [neg_zero, two_mul]
  exact le_rfl

end
end StatMech.FrontierA
