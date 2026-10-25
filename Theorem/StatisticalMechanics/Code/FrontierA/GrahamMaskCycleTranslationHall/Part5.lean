/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskCycleTranslationHall.Part5
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

open StatMech.Sharpness.RandomCurrent


theorem cycleTranslateMinBadPair_spec
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    ∀ base : leftMaskFiber ends m j k l zero p ×
        rightMaskFiber ends m j k l zero p,
      cycleTranslateBadCount ends m j k l zero p
          (cycleTranslateMinBadPair
            ends m j k l zero hloop hjk hkl hk0 p c) ≤
        cycleTranslateBadCount ends m j k l zero p base := by
  let q := Classical.choice
    (rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c)
  intro base
  exact (Classical.choose_spec
    ((Finset.univ : Finset
      (leftMaskFiber ends m j k l zero p ×
        rightMaskFiber ends m j k l zero p)).exists_min_image
      (cycleTranslateBadCount ends m j k l zero p)
      ⟨(c, q), Finset.mem_univ _⟩)).2 base (Finset.mem_univ _)


theorem card_leftMaskFiber_le_rightMaskFiber_of_minBadCount_zero
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p)
    (hzero : cycleTranslateBadCount ends m j k l zero p
      (cycleTranslateMinBadPair
        ends m j k l zero hloop hjk hkl hk0 p c) = 0) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) := by
  let base := cycleTranslateMinBadPair
    ends m j k l zero hloop hjk hkl hk0 p c
  apply card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslate
    ends m j k l zero p base.1 base.2
  exact (cycleTranslateBadCount_eq_zero_iff
    ends m j k l zero p base).mp hzero


theorem rowDataRepairHall_of_cycleTranslate_orbits
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (horbit : ∀ p : Finset I × Finset I,
      Nonempty (leftMaskFiber ends m j k l zero p) ->
        ∃ a : leftMaskFiber ends m j k l zero p,
          ∃ q : rightMaskFiber ends m j k l zero p,
            ∀ c : leftMaskFiber ends m j k l zero p,
              RowsDisconnect ends m
                (rightMaskCycleTranslate m a.1.1 c.1.1 q.1.1) k zero) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_maskwise
  intro p
  by_cases hleft : Nonempty (leftMaskFiber ends m j k l zero p)
  · obtain ⟨a, q, hgate⟩ := horbit p hleft
    exact card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslate
      ends m j k l zero p a q hgate
  · have hempty : IsEmpty (leftMaskFiber ends m j k l zero p) :=
      not_nonempty_iff.mp hleft
    simp


theorem rowDataRepairHall_of_minCycleTranslateBadCount_zero
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hzero : ∀ (p : Finset I × Finset I)
      (c : leftMaskFiber ends m j k l zero p),
      cycleTranslateBadCount ends m j k l zero p
        (cycleTranslateMinBadPair
          ends m j k l zero hloop hjk hkl hk0 p c) = 0) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_cycleTranslate_orbits
  intro p hleft
  let c := Classical.choice hleft
  let base := cycleTranslateMinBadPair
    ends m j k l zero hloop hjk hkl hk0 p c
  refine ⟨base.1, base.2, ?_⟩
  exact (cycleTranslateBadCount_eq_zero_iff
    ends m j k l zero p base).mp (hzero p c)


theorem rowDataRepairHall_of_cycleTranslate_respectsCuts
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hcuts : ∀ p : Finset I × Finset I,
      Nonempty (leftMaskFiber ends m j k l zero p) ->
        ∃ a : leftMaskFiber ends m j k l zero p,
          ∃ q : rightMaskFiber ends m j k l zero p,
            ∀ c : leftMaskFiber ends m j k l zero p,
              RightMaskCycleDifferenceRespectsCuts ends m
                (rowClass m q.1.1 0)
                (rightMaskCycleDifference m a.1.1 c.1.1) k) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_cycleTranslate_orbits
  intro p hleft
  obtain ⟨a, q, hq⟩ := hcuts p hleft
  refine ⟨a, q, fun c => ?_⟩
  exact rightMaskCycleTranslate_disconnects_of_respectsCuts
    ends m k zero a.1.1 c.1.1 q.1.1
      (a.2.trans c.2.symm) (a.2.trans q.2.symm) q.1.2.2.2.2.2
      (hq c)


theorem rowDataRepairHall_of_cycleTranslate_no_crossing_edges
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hno : ∀ p : Finset I × Finset I,
      Nonempty (leftMaskFiber ends m j k l zero p) ->
        ∃ a : leftMaskFiber ends m j k l zero p,
          ∃ q : rightMaskFiber ends m j k l zero p,
            ∀ c : leftMaskFiber ends m j k l zero p,
              (∀ e ∈ rightMaskCycleDifference m a.1.1 c.1.1,
                ¬ CrossesRootComponentCut
                  ends (rowClass m q.1.1 0) k e) ∧
              ∀ e ∈ rightMaskCycleDifference m a.1.1 c.1.1,
                ¬ CrossesRootComponentCut
                  ends (rowClass m q.1.1 1) k e) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_cycleTranslate_orbits
  intro p hleft
  obtain ⟨a, q, hq⟩ := hno p hleft
  refine ⟨a, q, fun c => ?_⟩
  exact rightMaskCycleTranslate_disconnects_of_no_crossing_edges
    ends m k zero a.1.1 c.1.1 q.1.1
      (a.2.trans c.2.symm) (a.2.trans q.2.symm) q.1.2.2.2.2.2
      (hq c).1 (hq c).2

end StatMech.GrahamGHS.FourColor
