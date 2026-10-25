/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle.Part5
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem leftMaskFiber_card_le_cycleProduct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (boundarySector ends p.1 ∅) *
        Fintype.card (boundarySector ends p.2 ∅) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_le_of_embedding
    (leftMaskCycleEmbedding ends m j k l zero p)


theorem rightMaskFiber_card_le_cycleProduct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (rightMaskFiber ends m j k l zero p) ≤
      Fintype.card (boundarySector ends p.1 ∅) *
        Fintype.card (boundarySector ends p.2 ∅) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_le_of_embedding
    (rightMaskCycleEmbedding ends m j k l zero p)


theorem rowDataRepairHall_of_cycleProduct_le_one
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hcycle : forall p : Finset I × Finset I,
      Fintype.card (boundarySector ends p.1 ∅) *
        Fintype.card (boundarySector ends p.2 ∅) ≤ 1) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_subsingleton_leftMaskFibers
    ends m j k l zero hloop hjk hkl hk0
  intro p
  rw [← Fintype.card_le_one_iff_subsingleton]
  exact (leftMaskFiber_card_le_cycleProduct ends m j k l zero p).trans
    (hcycle p)


theorem rowDataRepairHall_of_cycleProduct_le_two_of_rightPairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hcycle : forall p : Finset I × Finset I,
      Fintype.card (boundarySector ends p.1 ∅) *
        Fintype.card (boundarySector ends p.2 ∅) ≤ 2)
    (hpair : forall (p : Finset I × Finset I)
        (c d : leftMaskFiber ends m j k l zero p), c ≠ d ->
      ∃ q r : rightMaskFiber ends m j k l zero p, q ≠ r) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_maskwise
  intro p
  have hleft := (leftMaskFiber_card_le_cycleProduct
    ends m j k l zero p).trans (hcycle p)
  by_cases hsmall : Fintype.card (leftMaskFiber ends m j k l zero p) ≤ 1
  · by_cases hempty : Fintype.card (leftMaskFiber ends m j k l zero p) = 0
    · omega
    · have hpos : 0 < Fintype.card (leftMaskFiber ends m j k l zero p) := by
        omega
      let c := Classical.choice (Fintype.card_pos_iff.mp hpos)
      have hright : Nonempty (rightMaskFiber ends m j k l zero p) :=
        rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c
      have hrightPos : 0 < Fintype.card (rightMaskFiber ends m j k l zero p) :=
        Fintype.card_pos_iff.mpr hright
      omega
  · have hleftGt : 1 < Fintype.card (leftMaskFiber ends m j k l zero p) := by
      omega
    letI : Nontrivial (leftMaskFiber ends m j k l zero p) :=
      Fintype.one_lt_card_iff_nontrivial.mp hleftGt
    obtain ⟨c, d, hcd⟩ := exists_pair_ne
      (leftMaskFiber ends m j k l zero p)
    obtain ⟨q, r, hqr⟩ := hpair p c d hcd
    letI : Nontrivial (rightMaskFiber ends m j k l zero p) :=
      ⟨⟨q, r, hqr⟩⟩
    have hrightGt : 1 < Fintype.card
        (rightMaskFiber ends m j k l zero p) := Fintype.one_lt_card
    omega

end StatMech.GrahamGHS.FourColor
