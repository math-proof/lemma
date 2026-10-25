/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterEventFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Def.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterEventFKG


namespace StatMech.FrontierD

noncomputable section

theorem fkRectFiniteEventIntersection_isIncreasing
    {R : FKRectTorus} {ι : Type*} (s : Finset ι)
    (A : ι → Set R.Configuration) (hA : ∀ i ∈ s, IsIncreasing (A i)) :
    IsIncreasing (fkRectFiniteEventIntersection s A) := by
  intro omega tau hot hmem i hi
  exact hA i hi hot (hmem i hi)

theorem fkRectFiniteEventIntersection_isDecreasing
    {R : FKRectTorus} {ι : Type*} (s : Finset ι)
    (A : ι → Set R.Configuration) (hA : ∀ i ∈ s, IsDecreasing (A i)) :
    IsDecreasing (fkRectFiniteEventIntersection s A) := by
  intro omega tau hot hmem i hi
  exact hA i hi hot (hmem i hi)


theorem fkRectCriticalEventMass_prod_le_finiteIntersection
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {ι : Type*} (s : Finset ι) (A : ι → Set R.Configuration)
    (hA : ∀ i ∈ s, IsIncreasing (A i)) :
    (∏ i ∈ s, fkRectCriticalEventMass R q (A i)) ≤
      fkRectCriticalEventMass R q (fkRectFiniteEventIntersection s A) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [fkRectFiniteEventIntersection,
        fkRectCriticalEventMass_univ R (lt_of_lt_of_le zero_lt_one hq)]
  | @insert i s hi ih =>
      have hAi : IsIncreasing (A i) := hA i (Finset.mem_insert_self i s)
      have hAs : ∀ j ∈ s, IsIncreasing (A j) := by
        intro j hj
        exact hA j (Finset.mem_insert_of_mem hj)
      have hnonneg : 0 ≤ fkRectCriticalEventMass R q (A i) :=
        fkRectCriticalEventMass_nonneg R (lt_of_lt_of_le zero_lt_one hq) _
      calc
        (∏ j ∈ insert i s, fkRectCriticalEventMass R q (A j)) =
            fkRectCriticalEventMass R q (A i) *
              ∏ j ∈ s, fkRectCriticalEventMass R q (A j) := by
          rw [Finset.prod_insert hi]
        _ ≤ fkRectCriticalEventMass R q (A i) *
              fkRectCriticalEventMass R q
                (fkRectFiniteEventIntersection s A) :=
          mul_le_mul_of_nonneg_left (ih hAs) hnonneg
        _ ≤ fkRectCriticalEventMass R q
              (A i ∩ fkRectFiniteEventIntersection s A) :=
          fkRectCriticalEventMass_mul_le_inter R hq hAi
            (fkRectFiniteEventIntersection_isIncreasing s A hAs)
        _ = fkRectCriticalEventMass R q
              (fkRectFiniteEventIntersection (insert i s) A) := by
          congr 1
          ext omega
          simp [fkRectFiniteEventIntersection]


theorem fkRectCriticalEventMass_prod_le_finiteIntersection_decreasing
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    {ι : Type*} (s : Finset ι) (A : ι → Set R.Configuration)
    (hA : ∀ i ∈ s, IsDecreasing (A i)) :
    (∏ i ∈ s, fkRectCriticalEventMass R q (A i)) ≤
      fkRectCriticalEventMass R q (fkRectFiniteEventIntersection s A) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [fkRectFiniteEventIntersection,
        fkRectCriticalEventMass_univ R (lt_of_lt_of_le zero_lt_one hq)]
  | @insert i s hi ih =>
      have hAi : IsDecreasing (A i) := hA i (Finset.mem_insert_self i s)
      have hAs : ∀ j ∈ s, IsDecreasing (A j) := by
        intro j hj
        exact hA j (Finset.mem_insert_of_mem hj)
      have hnonneg : 0 ≤ fkRectCriticalEventMass R q (A i) :=
        fkRectCriticalEventMass_nonneg R (lt_of_lt_of_le zero_lt_one hq) _
      calc
        (∏ j ∈ insert i s, fkRectCriticalEventMass R q (A j)) =
            fkRectCriticalEventMass R q (A i) *
              ∏ j ∈ s, fkRectCriticalEventMass R q (A j) := by
          rw [Finset.prod_insert hi]
        _ ≤ fkRectCriticalEventMass R q (A i) *
              fkRectCriticalEventMass R q
                (fkRectFiniteEventIntersection s A) :=
          mul_le_mul_of_nonneg_left (ih hAs) hnonneg
        _ ≤ fkRectCriticalEventMass R q
              (A i ∩ fkRectFiniteEventIntersection s A) :=
          fkRectCriticalEventMass_mul_le_inter_decreasing R hq hAi
            (fkRectFiniteEventIntersection_isDecreasing s A hAs)
        _ = fkRectCriticalEventMass R q
              (fkRectFiniteEventIntersection (insert i s) A) := by
          congr 1
          ext omega
          simp [fkRectFiniteEventIntersection]


end
end StatMech.FrontierD
