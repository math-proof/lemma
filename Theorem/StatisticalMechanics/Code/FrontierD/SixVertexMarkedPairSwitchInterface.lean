/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairSwitchInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTorusBridge.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairSwitchInterface
open Finset Matrix Polynomial


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexMarkedSectorConfigurationPolynomial_eq_trace
    (T : EvenTorus) (n : Fin (T.width + 1)) :
    sixVertexMarkedSectorConfigurationPolynomial T n =
      sixVertexShiftedSectorTracePolynomial T.width T.height n.val := by
  rw [← sixVertexTorusMarkedSectorPartitionPolynomial_eq_trace T n]
  unfold sixVertexMarkedSectorConfigurationPolynomial
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun omega : SixVertexArrows T =>
      omega.IceRule /\
        sixVertexUpCount
          (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val)
    (by simp) (fun omega => sixVertexTorusMarkedWeight omega)]
  rw [Finset.sum_filter]
  unfold sixVertexTorusMarkedSectorPartitionPolynomial
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hice : omega.IceRule
  · by_cases hsector : sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val <;>
      simp [hice, hsector]
  · rw [sixVertexTorusMarkedWeight_eq_zero_of_not_ice omega hice]
    simp [hice]


end
end StatMech.FrontierD
