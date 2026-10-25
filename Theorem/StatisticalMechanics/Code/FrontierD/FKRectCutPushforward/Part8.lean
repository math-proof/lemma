/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part8
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

theorem fkRectCriticalEventMass_nonneg
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    0 ≤ fkRectCriticalEventMass R q A := by
  unfold fkRectCriticalEventMass
  apply Finset.sum_nonneg
  intro omega homega
  exact Set.indicator_nonneg
    (fun _ _ => fkRectCriticalRandomClusterProb_nonneg R hq _) _

theorem fkRectCriticalEventMass_mono
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    {A B : Set R.Configuration} (hAB : A ⊆ B) :
    fkRectCriticalEventMass R q A ≤ fkRectCriticalEventMass R q B := by
  unfold fkRectCriticalEventMass
  apply Finset.sum_le_sum
  intro omega homega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA, Set.indicator_of_mem (hAB hA)]
  · rw [Set.indicator_of_notMem hA]
    exact Set.indicator_nonneg
      (fun _ _ => fkRectCriticalRandomClusterProb_nonneg R hq _) _

theorem fkRectCriticalEventMass_cutClosed_eq_closedMass
    (R : FKRectTorus) (q : Real) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta} =
      fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) := by
  classical
  unfold fkRectCriticalEventMass fkRectCriticalClosedMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro eta heta
  by_cases hclosed : FKRectCutClosedConfiguration R eta
  · have hall := (fkRectCutClosedConfiguration_iff R eta).1 hclosed
    have hmem : eta ∈ {eta | FKRectCutClosedConfiguration R eta} := hclosed
    rw [Set.indicator_of_mem hmem, if_pos hall]
  · have hnotall : ¬ ∀ a ∈ fkRectTorusCutEdges R, eta a = false :=
      fun hall => hclosed ((fkRectCutClosedConfiguration_iff R eta).2 hall)
    have hnotmem : eta ∉ {eta | FKRectCutClosedConfiguration R eta} :=
      hclosed
    rw [Set.indicator_of_notMem hnotmem, if_neg hnotall]


end
end StatMech.FrontierD
