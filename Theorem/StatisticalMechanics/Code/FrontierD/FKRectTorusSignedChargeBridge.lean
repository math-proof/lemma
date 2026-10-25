/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSignedChargeBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4ParameterBridge
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSignedChargeBridge
open scoped BigOperators
open Matrix


namespace StatMech.FrontierD

noncomputable section

theorem fkRectOrientedLoopPartitionSum_eq_generic
    (R : FKRectTorus) (lam : Real) :
    fkRectOrientedLoopPartitionSum R lam =
      fkOrientedLoopPartitionSum R.medialTorus lam := by
  unfold fkRectOrientedLoopPartitionSum fkOrientedLoopPartitionSum
    fkRectOrientedLoopWeight
  rw [Equiv.sum_comp (fkRectConfigurationToMedialPairing R)
    (fun pairing => ∑ arrows : SixVertexArrows R.medialTorus,
      fkOrientedLoopPairingWeight lam pairing arrows)]
  rw [Finset.sum_comm]

theorem fkRectOrientedLoopPartitionSum_eq_sixVertex
    (R : FKRectTorus) (lam : Real) :
    fkRectOrientedLoopPartitionSum R lam =
      sixVertexTorusArrowPartitionSum R.medialTorus
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) := by
  rw [fkRectOrientedLoopPartitionSum_eq_generic]
  exact fkOrientedLoopPartitionSum_eq_sixVertexTorusArrowPartitionSum _ _


end
end StatMech.FrontierD
