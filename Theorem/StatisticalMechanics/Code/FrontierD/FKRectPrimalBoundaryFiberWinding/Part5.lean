/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalBoundaryFiberWinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Theorem.StatisticalMechanics.Code.FrontierD.PermCycleQuotientWeightSum
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalBoundaryFiberWinding.Part4
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 800000 in


theorem fkRectBlackBoundaryCycle_eq_of_card_nonzero_le_two_of_fst_mul_pos
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (hcard : (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2)
    {C D : FKRectConfigurationBlackBoundaryCycle R omega}
    (hC : fkRectBlackBoundaryCycleInPrimalCluster R omega x C)
    (hD : fkRectBlackBoundaryCycleInPrimalCluster R omega x D)
    (hsign : 0 < (fkRectBlackBoundaryCycleWinding R omega C).1 *
      (fkRectBlackBoundaryCycleWinding R omega D).1) :
    C = D := by
  classical
  apply eq_of_sum_ite_eq_zero_of_card_nonzero_le_two_of_fst_mul_pos
    (fun A : FKRectConfigurationBlackBoundaryCycle R omega =>
      fkRectBlackBoundaryCycleInPrimalCluster R omega x A)
    (fkRectBlackBoundaryCycleWinding R omega)
    (fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero R omega x)
    (by simpa [fkRectPrimalClusterNonzeroBoundaryCycles] using hcard)
    hC hD hsign

end
end StatMech.FrontierD
