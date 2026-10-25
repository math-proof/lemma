/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutFiberReduction.Part8
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryCycleDuality.Part3
open Equiv SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBlackBoundaryCycleInPrimalCluster_iff_primalComponent
    (R : FKRectTorus) (omega : R.Configuration) (x : R.Vertex)
    (C : FKRectConfigurationBlackBoundaryCycle R omega) :
    fkRectBlackBoundaryCycleInPrimalCluster R omega x C ↔
      fkRectBlackBoundaryCyclePrimalComponent R omega C =
        (fkRectOpenGraph R omega).connectedComponentMk x := by
  induction C using Quot.ind with
  | _ d =>
      rw [fkRectBlackBoundaryCycleInPrimalCluster_mk,
        fkRectBlackBoundaryCyclePrimalComponent_mk,
        ConnectedComponent.eq]
      exact ⟨fun h => h.symm, fun h => h.symm⟩


end
end StatMech.FrontierD
