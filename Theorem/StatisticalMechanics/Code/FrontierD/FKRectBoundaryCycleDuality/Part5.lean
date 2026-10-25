/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleDuality.Part4
open Equiv SimpleGraph


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 600000 in


theorem fkRectDualClusterBoundaryCycleWindingSum_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (L : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent) :
    fkRectDualClusterBoundaryCycleWindingSum R omega L = 0 := by
  classical
  let dual := fkRectDualConfigurationEquiv R omega
  let e := fkRectBlackBoundaryCycleDualEquiv R omega
  have hzero := fkRectPrimalClusterBoundaryCycleWindingSum_eq_zero
    R dual L.out
  unfold fkRectPrimalClusterBoundaryCycleWindingSum at hzero
  have hcomponent (D : FKRectConfigurationBlackBoundaryCycle R dual) :
      fkRectBlackBoundaryCycleInPrimalCluster R dual L.out D ↔
        fkRectBlackBoundaryCyclePrimalComponent R dual D = L := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent]
    have hout : (fkRectOpenGraph R dual).connectedComponentMk L.out = L := by
      exact L.out_eq
    rw [hout]
  simp_rw [hcomponent] at hzero
  rw [← e.sum_comp] at hzero
  unfold fkRectDualClusterBoundaryCycleWindingSum
  have hreindexed :
      (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if fkRectBlackBoundaryCycleDualComponent R omega C = L then
          -fkRectBlackBoundaryCycleWinding R omega C else 0) = 0 := by
    simpa only [fkRectBlackBoundaryCycleWinding_dualEquiv,
      fkRectBlackBoundaryCycleDualComponent, dual, e] using hzero
  have hneg :
      -(∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if fkRectBlackBoundaryCycleDualComponent R omega C = L then
          fkRectBlackBoundaryCycleWinding R omega C else 0) = 0 := by
    calc
      _ = ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
          -(if fkRectBlackBoundaryCycleDualComponent R omega C = L then
            fkRectBlackBoundaryCycleWinding R omega C else 0) := by
        rw [Finset.sum_neg_distrib]
      _ = ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
          if fkRectBlackBoundaryCycleDualComponent R omega C = L then
            -fkRectBlackBoundaryCycleWinding R omega C else 0 := by
        apply Finset.sum_congr rfl
        intro C _
        split <;> simp_all
      _ = 0 := hreindexed
  exact neg_eq_zero.mp hneg

end
end StatMech.FrontierD
