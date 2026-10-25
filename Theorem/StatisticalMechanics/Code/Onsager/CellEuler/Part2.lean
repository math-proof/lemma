/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellCount.Part2
import Def.StatisticalMechanics.Code.Onsager.CellEuler.Part2


namespace StatMech.Onsager.CellEuler

open Finset StatMech.Onsager.CellCount


theorem cornerCount_pos_iff_mem (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    0 < cornerCount S v ↔ v ∈ cellVerts S := by
  unfold cornerCount cellVerts
  rw [Finset.card_pos]
  constructor
  · rintro ⟨c, hc⟩
    rw [Finset.mem_filter] at hc
    exact Finset.mem_biUnion.mpr ⟨c, hc.1, hc.2⟩
  · intro hv
    obtain ⟨c, hcS, hvc⟩ := Finset.mem_biUnion.mp hv
    exact ⟨c, Finset.mem_filter.mpr ⟨hcS, hvc⟩⟩


theorem cornerWeight_zero : cornerWeight 0 = 0 := by unfold cornerWeight; decide


theorem cornerDiff_eq_sum (S : Finset (ℤ × ℤ)) :
    cornerDiff S = ∑ v ∈ cellVerts S, cornerWeight (cornerCount S v) := by
  unfold cornerDiff cornerWeight
  rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_boole]


theorem cornerDiff_insert (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ) (hc : c ∉ S) :
    cornerDiff (insert c S)
      = cornerDiff S + ∑ v ∈ cornersOf c,
          (cornerWeight (cornerCount S v + 1) - cornerWeight (cornerCount S v)) := by
  have hsub : cornerDiff S
      = ∑ v ∈ cornersOf c ∪ cellVerts S, cornerWeight (cornerCount S v) := by
    rw [cornerDiff_eq_sum]
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hvnot
    have hz : cornerCount S v = 0 := by
      by_contra h
      exact hvnot ((cornerCount_pos_iff_mem S v).mp (Nat.pos_of_ne_zero h))
    rw [hz, cornerWeight_zero]
  have hexpand :
      ∑ v ∈ cornersOf c ∪ cellVerts S,
          (if v ∈ cornersOf c then
            cornerWeight (cornerCount S v + 1) - cornerWeight (cornerCount S v) else 0)
        = ∑ v ∈ cornersOf c,
          (cornerWeight (cornerCount S v + 1) - cornerWeight (cornerCount S v)) := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_left]
  rw [cornerDiff_eq_sum, cellVerts_insert, hsub, ← hexpand, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [cornerCount_insert S c hc v]
  by_cases h : v ∈ cornersOf c
  · simp only [if_pos h]; ring
  · simp only [if_neg h, add_zero]


theorem cornerCount_singleton_eq_one (c v : ℤ × ℤ) (hv : v ∈ cornersOf c) :
    cornerCount ({c} : Finset (ℤ × ℤ)) v = 1 := by
  unfold cornerCount
  rw [Finset.filter_singleton, if_pos hv, Finset.card_singleton]


theorem cornerCount_singleton_eq_zero (c v : ℤ × ℤ) (hv : v ∉ cornersOf c) :
    cornerCount ({c} : Finset (ℤ × ℤ)) v = 0 := by
  unfold cornerCount
  rw [Finset.filter_singleton, if_neg hv, Finset.card_empty]


theorem cellVerts_singleton (c : ℤ × ℤ) : cellVerts ({c} : Finset (ℤ × ℤ)) = cornersOf c := by
  unfold cellVerts; rw [Finset.singleton_biUnion]


theorem cornerDiff_singleton (c : ℤ × ℤ) : cornerDiff ({c} : Finset (ℤ × ℤ)) = 4 := by
  unfold cornerDiff
  rw [cellVerts_singleton]
  have hconv : (cornersOf c).filter (fun v => cornerCount ({c} : Finset (ℤ × ℤ)) v = 1)
      = cornersOf c := by
    apply Finset.filter_true_of_mem
    intro v hv
    exact cornerCount_singleton_eq_one c v hv
  have hrefl : (cornersOf c).filter (fun v => cornerCount ({c} : Finset (ℤ × ℤ)) v = 3)
      = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro v hv
    rw [cornerCount_singleton_eq_one c v hv]
    decide
  rw [hconv, hrefl, cornersOf_card, Finset.card_empty]
  decide


theorem cornerCount_eq_inter (S : Finset (ℤ × ℤ)) (v : ℤ × ℤ) :
    cornerCount S v
      = (S ∩ ({v, (v.1 - 1, v.2), (v.1, v.2 - 1), (v.1 - 1, v.2 - 1)} : Finset (ℤ × ℤ))).card := by
  unfold cornerCount
  congr 1
  ext c'
  rw [Finset.mem_filter, Finset.mem_inter, mem_cornersOf_iff]
  simp only [mem_insert, mem_singleton]


end StatMech.Onsager.CellEuler
