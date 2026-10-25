/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkRectHorizontalCutClosedConfiguration_force
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectHorizontalCutClosedConfiguration R
      (fkRectForceHorizontalCutClosed R omega) := by
  intro a ha
  simp [fkRectForceHorizontalCutClosed, fkRectForceEdgesClosed, ha]

theorem fkRectCriticalEventMass_horizontalCutClosed_eq_closedMass
    (R : FKRectTorus) (q : Real) :
    fkRectCriticalEventMass R q
        {eta | FKRectHorizontalCutClosedConfiguration R eta} =
      fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) := by
  classical
  unfold fkRectCriticalEventMass fkRectCriticalClosedMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro eta _
  by_cases hclosed : FKRectHorizontalCutClosedConfiguration R eta
  · rw [Set.indicator_of_mem hclosed,
      if_pos (show ∀ a ∈ fkRectHorizontalCutEdges R, eta a = false from
        hclosed)]
  · rw [Set.indicator_of_notMem hclosed,
      if_neg (show ¬∀ a ∈ fkRectHorizontalCutEdges R, eta a = false from
        hclosed)]

theorem fkRectCriticalClosedMass_horizontalCut_pos
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) :
    0 < fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) := by
  have hlower := fkRectCritical_cFE_pow_le_closedMass
    R hq (fkRectHorizontalCutEdges R)
  have hc : 0 < FK.cFE (fkRectCriticalP q) q :=
    FK.cFE_pos
      (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
      (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq
  exact (pow_pos hc _).trans_le hlower

theorem fkRectCriticalClosedMass_horizontalCut_le_one
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) :
    fkRectCriticalClosedMass R q (fkRectHorizontalCutEdges R) <= 1 := by
  rw [← fkRectCriticalEventMass_horizontalCutClosed_eq_closedMass]
  calc
    fkRectCriticalEventMass R q
        {eta | FKRectHorizontalCutClosedConfiguration R eta} <=
      fkRectCriticalEventMass R q Set.univ :=
        fkRectCriticalEventMass_mono R
          (lt_of_lt_of_le zero_lt_one hq) (Set.subset_univ _)
    _ = 1 := by
      unfold fkRectCriticalEventMass
      simpa using sum_fkRectCriticalRandomClusterProb R
        (lt_of_lt_of_le zero_lt_one hq)


end
end StatMech.FrontierD
