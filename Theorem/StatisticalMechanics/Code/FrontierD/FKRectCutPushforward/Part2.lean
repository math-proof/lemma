/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part2
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

theorem fkRectGraphCriticalEventMass_mono
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    {A B : Set (FKRectGraphConfiguration R)} (hAB : A ⊆ B) :
    fkRectGraphCriticalEventMass R q A ≤
      fkRectGraphCriticalEventMass R q B := by
  unfold fkRectGraphCriticalEventMass
  apply Finset.sum_le_sum
  intro eta heta
  by_cases hA : eta ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hAB hA)]
  · rw [Set.indicator_of_notMem hA]
    exact Set.indicator_nonneg
      (fun _ _ => fkRectGraphCriticalRandomClusterProb_nonneg R hq _) _

end
end StatMech.FrontierD
