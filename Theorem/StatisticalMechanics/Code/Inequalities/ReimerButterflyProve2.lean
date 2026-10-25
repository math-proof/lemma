/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyProve2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyProve.Part2
import Mathlib.Combinatorics.SetFamily.Compression.Down
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


theorem downComp_nonMemberSubfamily (i : α) (𝒜 : Finset (Finset α)) :
    (Down.compression i 𝒜).nonMemberSubfamily i
      = 𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i := by
  ext s
  simp only [mem_nonMemberSubfamily, mem_union, mem_memberSubfamily, Down.mem_compression]
  constructor
  · rintro ⟨h, hns⟩
    rcases h with ⟨hin, _⟩ | ⟨_, hins⟩
    · exact Or.inr ⟨hin, hns⟩
    · exact Or.inl ⟨hins, hns⟩
  · rintro (⟨hins, hns⟩ | ⟨hin, hns⟩)
    · refine ⟨?_, hns⟩
      by_cases hsA : s ∈ 𝒜
      · exact Or.inl ⟨hsA, by rw [erase_eq_of_notMem hns]; exact hsA⟩
      · exact Or.inr ⟨hsA, hins⟩
    · exact ⟨Or.inl ⟨hin, by rw [erase_eq_of_notMem hns]; exact hin⟩, hns⟩


theorem downComp_memberSubfamily (i : α) (𝒜 : Finset (Finset α)) :
    (Down.compression i 𝒜).memberSubfamily i
      = 𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i := by
  ext s
  simp only [mem_memberSubfamily, mem_inter, mem_nonMemberSubfamily, Down.mem_compression]
  constructor
  · rintro ⟨h, hns⟩
    rcases h with ⟨hin, herase⟩ | ⟨hnin, hins⟩
    · rw [erase_insert hns] at herase; exact ⟨⟨hin, hns⟩, herase, hns⟩
    · rw [insert_idem] at hins; exact absurd hins hnin
  · rintro ⟨⟨hin, hns⟩, hsA, _⟩
    exact ⟨Or.inl ⟨hin, by rw [erase_insert hns]; exact hsA⟩, hns⟩


theorem dpairsCount_double_sum (𝒜 ℬ : Finset (Finset α)) :
    dpairsCount 𝒜 ℬ = ∑ S ∈ 𝒜, ∑ T ∈ ℬ, (if Disjoint S T then 1 else 0) := by
  unfold dpairsCount
  rw [Finset.card_filter, Finset.sum_product]


theorem dpairsCount_mono_left {𝒜 𝒜' : Finset (Finset α)} (ℬ : Finset (Finset α))
    (h : 𝒜 ⊆ 𝒜') : dpairsCount 𝒜 ℬ ≤ dpairsCount 𝒜' ℬ := by
  rw [dpairsCount_double_sum, dpairsCount_double_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro S _ _; exact Finset.sum_nonneg (fun T _ => by split <;> simp)


theorem dpairsCount_mono_right (𝒞 : Finset (Finset α)) {ℬ ℬ' : Finset (Finset α)}
    (h : ℬ ⊆ ℬ') : dpairsCount 𝒞 ℬ ≤ dpairsCount 𝒞 ℬ' := by
  rw [dpairsCount_double_sum, dpairsCount_double_sum]
  apply Finset.sum_le_sum; intro S _
  apply Finset.sum_le_sum_of_subset_of_nonneg h
  intro T _ _; split <;> simp


theorem dpairsCount_modular_left (𝒜 ℬ 𝒞 : Finset (Finset α)) :
    dpairsCount (𝒜 ∪ ℬ) 𝒞 + dpairsCount (𝒜 ∩ ℬ) 𝒞
      = dpairsCount 𝒜 𝒞 + dpairsCount ℬ 𝒞 := by
  simp only [dpairsCount_double_sum]; exact Finset.sum_union_inter


theorem dpairsCount_modular_right (𝒜 ℬ 𝒞 : Finset (Finset α)) :
    dpairsCount 𝒞 (𝒜 ∪ ℬ) + dpairsCount 𝒞 (𝒜 ∩ ℬ)
      = dpairsCount 𝒞 𝒜 + dpairsCount 𝒞 ℬ := by
  simp only [dpairsCount_double_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun S _ => Finset.sum_union_inter)


theorem dpairsCount_fiber_downDown_ineq (am an bm bn : Finset (Finset α)) :
    dpairsCount an bn + dpairsCount am bn + dpairsCount an bm
      ≤ dpairsCount (am ∪ an) (bm ∪ bn) + dpairsCount (am ∩ an) (bm ∪ bn)
        + dpairsCount (am ∪ an) (bm ∩ bn) := by
  have e1 := dpairsCount_modular_left am an (bm ∪ bn)
  have e2 := dpairsCount_modular_left am an (bm ∩ bn)
  have e3 := dpairsCount_modular_right bm bn am
  have e4 := dpairsCount_modular_right bm bn an
  have e5 := dpairsCount_modular_right bm bn (am ∩ an)
  have hmono : dpairsCount (am ∩ an) (bm ∩ bn) ≤ dpairsCount am bm :=
    le_trans (dpairsCount_mono_left _ Finset.inter_subset_left)
             (dpairsCount_mono_right _ Finset.inter_subset_left)
  omega


theorem dpairsCount_downDown_mono (𝒜 ℬ : Finset (Finset α)) (i : α) :
    dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) := by
  rw [dpairsCount_fiber_recursion 𝒜 ℬ i,
    dpairsCount_fiber_recursion (Down.compression i 𝒜) (Down.compression i ℬ) i,
    downComp_nonMemberSubfamily i 𝒜, downComp_memberSubfamily i 𝒜,
    downComp_nonMemberSubfamily i ℬ, downComp_memberSubfamily i ℬ]
  exact dpairsCount_fiber_downDown_ineq _ _ _ _

end StatMech
