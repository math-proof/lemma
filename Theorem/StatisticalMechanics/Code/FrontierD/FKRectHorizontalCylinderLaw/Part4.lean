/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectHorizontalCutClosedReducedEventWeight_univ
    (R : FKRectTorus) (q : Real) :
    fkRectHorizontalCutClosedReducedEventWeight R q Set.univ =
      fkRectHorizontalCutClosedReducedZ R q := by
  unfold fkRectHorizontalCutClosedReducedEventWeight
    fkRectHorizontalCutClosedReducedZ
  apply Finset.sum_congr rfl
  intro omega _
  rw [Set.indicator_of_mem (Set.mem_univ omega.1)]

theorem fkRectHorizontalCutClosedReducedZ_pos
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    0 < fkRectHorizontalCutClosedReducedZ R q := by
  unfold fkRectHorizontalCutClosedReducedZ
  apply Finset.sum_pos
  · intro omega _
    exact fkRectCriticalReducedWeight_pos R hq omega.1
  · let omega : FKRectHorizontalCutClosedConfig R :=
      ⟨fun _ => false, fun _ _ => rfl⟩
    exact ⟨omega, Finset.mem_univ omega⟩


theorem fkRect_horizontalCutClosed_indicatorReduced_sum
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    (∑ eta : R.Configuration,
      {eta | FKRectHorizontalCutClosedConfiguration R eta ∧
        eta ∈ A}.indicator
        (fun eta => fkRectCriticalReducedWeight R q eta) eta) =
      fkRectHorizontalCutClosedReducedEventWeight R q A := by
  classical
  calc
    (∑ eta : R.Configuration,
      {eta | FKRectHorizontalCutClosedConfiguration R eta ∧
        eta ∈ A}.indicator
        (fun eta => fkRectCriticalReducedWeight R q eta) eta) =
      ∑ eta : R.Configuration,
        if FKRectHorizontalCutClosedConfiguration R eta then
          A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta
        else 0 := by
      apply Finset.sum_congr rfl
      intro eta _
      by_cases hc : FKRectHorizontalCutClosedConfiguration R eta
      · by_cases hA : eta ∈ A <;> simp [hc, hA]
      · simp [hc]
    _ = ∑ eta ∈ (Finset.univ.filter
          (FKRectHorizontalCutClosedConfiguration R)),
        A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta := by
      rw [Finset.sum_filter]
    _ = ∑ eta : FKRectHorizontalCutClosedConfig R,
        A.indicator (fun eta => fkRectCriticalReducedWeight R q eta) eta.1 := by
      exact Finset.sum_subtype _ (by simp) _
    _ = fkRectHorizontalCutClosedReducedEventWeight R q A := rfl


theorem fkRectCriticalEventMass_horizontalCutClosed_inter_eq
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    fkRectCriticalEventMass R q
        {eta | FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} =
      fkRectHorizontalCutClosedReducedEventWeight R q A /
        fkRectCriticalReducedZ R q := by
  unfold fkRectCriticalEventMass fkRectCriticalRandomClusterProb
  calc
    (∑ eta : R.Configuration,
      {eta | FKRectHorizontalCutClosedConfiguration R eta ∧
        eta ∈ A}.indicator
        (fun eta => fkRectCriticalReducedWeight R q eta /
          fkRectCriticalReducedZ R q) eta) =
      (∑ eta : R.Configuration,
        {eta | FKRectHorizontalCutClosedConfiguration R eta ∧
          eta ∈ A}.indicator
          (fun eta => fkRectCriticalReducedWeight R q eta) eta) /
        fkRectCriticalReducedZ R q := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro eta _
      by_cases hmem :
          FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A
      · have hset : eta ∈ {eta : R.Configuration |
            FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} := hmem
        rw [Set.indicator_of_mem hset, Set.indicator_of_mem hset]
      · have hset : eta ∉ {eta : R.Configuration |
            FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ A} := hmem
        rw [Set.indicator_of_notMem hset,
          Set.indicator_of_notMem hset, zero_div]
    _ = _ := by rw [fkRect_horizontalCutClosed_indicatorReduced_sum]


theorem fkRectCriticalHorizontalCutEventMass_eq_reduced
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (A : Set R.Configuration) :
    fkRectCriticalHorizontalCutEventMass R q A =
      fkRectHorizontalCutClosedReducedEventWeight R q A /
        fkRectHorizontalCutClosedReducedZ R q := by
  unfold fkRectCriticalHorizontalCutEventMass
  rw [← fkRectCriticalEventMass_horizontalCutClosed_eq_closedMass,
    fkRectCriticalEventMass_horizontalCutClosed_inter_eq]
  have hden := fkRectCriticalEventMass_horizontalCutClosed_inter_eq
    R q Set.univ
  rw [show {eta : R.Configuration |
      FKRectHorizontalCutClosedConfiguration R eta ∧ eta ∈ Set.univ} =
      {eta | FKRectHorizontalCutClosedConfiguration R eta} by ext; simp,
    fkRectHorizontalCutClosedReducedEventWeight_univ] at hden
  rw [hden]
  have htotal : fkRectCriticalReducedZ R q ≠ 0 :=
    (fkRectCriticalReducedZ_pos R
      (lt_of_lt_of_le zero_lt_one hq)).ne'
  have hcyl : fkRectHorizontalCutClosedReducedZ R q ≠ 0 :=
    (fkRectHorizontalCutClosedReducedZ_pos R
      (lt_of_lt_of_le zero_lt_one hq)).ne'
  field_simp


end
end StatMech.FrontierD
