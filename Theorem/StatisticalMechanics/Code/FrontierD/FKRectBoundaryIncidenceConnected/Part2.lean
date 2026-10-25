/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleDuality.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualClusterLoopCount
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteBipartiteFlowSparse
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

set_option maxHeartbeats 600000 in


theorem fkRectDualBoundarySupportedFiberSum_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (L : (fkRectOpenGraph R
      (fkRectDualConfigurationEquiv R omega)).ConnectedComponent) :
    fkRectDualBoundarySupportedFiberSum R omega L = 0 := by
  classical
  let w := fkRectBlackBoundaryCycleWinding R omega
  let right := fkRectBlackBoundaryCycleDualComponent R omega
  unfold fkRectDualBoundarySupportedFiberSum
  change (∑ C ∈ ((Finset.univ : Finset
      (FKRectConfigurationBlackBoundaryCycle R omega)).filter fun C ↦
        w C ≠ 0).filter (fun C ↦ right C = L), w C) = 0
  have hzero := fkRectDualClusterBoundaryCycleWindingSum_eq_zero R omega L
  change (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
      if right C = L then w C else 0) = 0 at hzero
  rw [Finset.sum_filter, Finset.sum_filter]
  calc
    (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if w C ≠ 0 then
          if right C = L then w C else 0 else 0) =
      ∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
        if right C = L then w C else 0 := by
      apply Finset.sum_congr rfl
      intro C _
      by_cases hw : w C = 0 <;>
        by_cases hL : right C = L <;>
        simp [hw, hL]
    _ = 0 := hzero

set_option maxHeartbeats 800000 in


theorem card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two
    (R : FKRectTorus) (omega : R.Configuration)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2 := by
  classical
  have hcard := connectedBipartiteFlow_leftFiber_card_le_two
    (fkRectBlackBoundaryCyclePrimalComponent R omega)
    (fkRectBlackBoundaryCycleDualComponent R omega)
    (fkRectBlackBoundaryCycleWinding R omega)
    (fkRectBoundaryCycleIncidence_connected R omega)
    (card_boundaryCycles_le_incidentComponents R omega)
    (fun p => fkRectPrimalBoundarySupportedFiberSum_eq_zero R omega p)
    (fun d => by
      have h := fkRectDualBoundarySupportedFiberSum_eq_zero R omega d
      unfold fkRectDualBoundarySupportedFiberSum at h
      exact h) K
  have hcomponent (C : FKRectConfigurationBlackBoundaryCycle R omega) :
      fkRectBlackBoundaryCycleInPrimalCluster R omega K.out C ↔
        fkRectBlackBoundaryCyclePrimalComponent R omega C = K := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent,
      show (fkRectOpenGraph R omega).connectedComponentMk K.out = K from
        K.out_eq]
  simpa only [fkRectPrimalClusterNonzeroBoundaryCycles,
    Finset.mem_filter, Finset.mem_univ, true_and, hcomponent] using hcard

set_option maxHeartbeats 800000 in


theorem card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex) :
    (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2 := by
  let K := (fkRectOpenGraph R omega).connectedComponentMk x
  have h := card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two R omega K
  have hcomponent (C : FKRectConfigurationBlackBoundaryCycle R omega) :
      fkRectBlackBoundaryCycleInPrimalCluster R omega x C ↔
        fkRectBlackBoundaryCycleInPrimalCluster R omega K.out C := by
    rw [fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent,
      fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent,
      show (fkRectOpenGraph R omega).connectedComponentMk x = K from rfl,
      show (fkRectOpenGraph R omega).connectedComponentMk K.out = K from
        K.out_eq]
  have hset : fkRectPrimalClusterNonzeroBoundaryCycles R omega x =
      fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out := by
    ext C
    simp only [fkRectPrimalClusterNonzeroBoundaryCycles,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr (hcomponent C) Iff.rfl
  rw [hset]
  exact h


theorem card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_not_hasNet
    (R : FKRectTorus) (omega : R.Configuration)
    (_hnoNet : ¬ FKRectHasNet R omega)
    (K : (fkRectOpenGraph R omega).ConnectedComponent) :
    (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2 :=
  card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two R omega K

end
end StatMech.FrontierD
