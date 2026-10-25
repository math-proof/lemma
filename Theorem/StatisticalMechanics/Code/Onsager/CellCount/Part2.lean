/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.StatisticalMechanics.Code.Onsager.CellCount.Part2


namespace StatMech.Onsager.CellCount

open Finset


theorem cornerCount_le_four (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    cornerCount S v ≤ 4 := by
  unfold cornerCount
  have hsub : S.filter (fun c => v ∈ cornersOf c) ⊆ candCells v := by
    intro c hc
    rw [mem_filter, mem_cornersOf_iff] at hc
    unfold candCells
    simp only [mem_insert, mem_singleton]
    tauto
  refine (card_le_card hsub).trans ?_
  unfold candCells
  refine (card_insert_le _ _).trans ?_
  refine (Nat.add_le_add_right (card_insert_le _ _) 1).trans ?_
  refine (Nat.add_le_add_right (Nat.add_le_add_right (card_insert_le _ _) 1) 1).trans ?_
  simp


theorem sum_cornerCount (S : Finset (ℤ × ℤ)) :
    ∑ v ∈ cellVerts S, cornerCount S v = 4 * S.card := by
  unfold cornerCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  have key : ∀ c ∈ S, (∑ v ∈ cellVerts S, if v ∈ cornersOf c then 1 else 0) = 4 := by
    intro c hc
    rw [← Finset.sum_filter]
    have hfe : (cellVerts S).filter (fun v => v ∈ cornersOf c) = cornersOf c := by
      ext v
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro hv
        exact ⟨Finset.mem_biUnion.mpr ⟨c, hc, hv⟩, hv⟩
    rw [hfe, Finset.sum_const, smul_eq_mul, mul_one]
    exact cornersOf_card c
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul, mul_comm]

end StatMech.Onsager.CellCount
