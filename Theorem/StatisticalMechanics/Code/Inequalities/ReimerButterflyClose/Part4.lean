/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyStep
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
import Mathlib.Combinatorics.SetFamily.Compression.Down
import Mathlib.Combinatorics.SetFamily.Compression.UV
import Def.StatisticalMechanics.Code.Inequalities.ReimerButterflyClose.Part3
open Finset
open scoped FinsetFamily


namespace StatMech

variable {α : Type*} [DecidableEq α]


section Weighted

variable [Fintype α]


theorem wdpairs_le_mul {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (𝒜 ℬ : Finset (Finset α)) :
    wdpairs w 𝒜 ℬ ≤ fmarg w 𝒜 * fmarg w ℬ := by
  unfold wdpairs fmarg
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p _ _
  exact mul_nonneg (fwt_nonneg hw _) (fwt_nonneg hw _)


theorem wdpairs'_le_mul {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α)
    (𝒜 ℬ : Finset (Finset α)) :
    wdpairs' w i 𝒜 ℬ ≤ fmarg' w i 𝒜 * fmarg' w i ℬ := by
  unfold wdpairs' fmarg'
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro p _ _
  exact mul_nonneg (fwt'_nonneg hw _ _) (fwt'_nonneg hw _ _)


theorem wdpairs'_nonneg {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b) (i : α)
    (𝒜 ℬ : Finset (Finset α)) : 0 ≤ wdpairs' w i 𝒜 ℬ := by
  unfold wdpairs'
  refine Finset.sum_nonneg (fun p _ => ?_)
  exact mul_nonneg (fwt'_nonneg hw _ _) (fwt'_nonneg hw _ _)


theorem fmarg_split (w : α → Bool → ℝ) (𝒜 : Finset (Finset α)) (i : α) :
    fmarg w 𝒜
      = w i true * fmarg' w i (𝒜.memberSubfamily i)
      + w i false * fmarg' w i (𝒜.nonMemberSubfamily i) := by
  classical
  unfold fmarg fmarg'
  rw [← Finset.sum_filter_add_sum_filter_not 𝒜 (fun S => i ∈ S)]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · rw [show 𝒜.memberSubfamily i = (𝒜.filter (fun S => i ∈ S)).image (fun S => S.erase i)
        from ?_]
    · rw [Finset.sum_image ?_]
      · apply Finset.sum_congr rfl
        intro S hS
        rw [Finset.mem_filter] at hS
        rw [fwt_of_mem w hS.2]
      · intro S hS T hT heq
        rw [Finset.mem_coe, Finset.mem_filter] at hS hT
        simp only [] at heq
        rw [← Finset.insert_erase hS.2, ← Finset.insert_erase hT.2, heq]
    · ext S
      simp only [Finset.mem_image, Finset.mem_filter, mem_memberSubfamily]
      constructor
      · rintro ⟨hins, hnotin⟩
        exact ⟨insert i S, ⟨hins, Finset.mem_insert_self _ _⟩, by rw [Finset.erase_insert hnotin]⟩
      · rintro ⟨T, ⟨hT, hiT⟩, rfl⟩
        rw [Finset.insert_erase hiT]
        exact ⟨hT, Finset.notMem_erase _ _⟩
  · apply Finset.sum_congr
    · ext S; simp only [Finset.mem_filter, mem_nonMemberSubfamily]
    · intro S hS
      rw [mem_nonMemberSubfamily] at hS
      rw [fwt_of_notMem w hS.2]


theorem wfiber_notMem_notMem (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (∑ p ∈ (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter
              (fun p => i ∉ p.1 ∧ i ∉ p.2)), fwt w p.1 * fwt w p.2)
    = w i false * w i false * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
  classical
  unfold wdpairs'
  rw [Finset.mul_sum]
  apply Finset.sum_nbij' (fun p => p) (fun p => p)
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product, mem_nonMemberSubfamily] at hp ⊢
    obtain ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩ := hp
    exact ⟨⟨⟨hS, hi1⟩, hT, hi2⟩, hd⟩
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product, mem_nonMemberSubfamily] at hp ⊢
    obtain ⟨⟨⟨hS, hi1⟩, hT, hi2⟩, hd⟩ := hp
    exact ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩
  · intro p _; rfl
  · intro p _; rfl
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp
    obtain ⟨_, hi1, hi2⟩ := hp
    rw [fwt_of_notMem w hi1, fwt_of_notMem w hi2]; ring


theorem wfiber_mem_fst (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (∑ p ∈ (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1)),
      fwt w p.1 * fwt w p.2)
    = w i true * w i false * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i) := by
  classical
  unfold wdpairs'
  rw [Finset.mul_sum]
  rw [show (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter (fun p => i ∈ p.1))
        = (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter
            (fun p => i ∈ p.1 ∧ i ∉ p.2)) from ?_]
  · apply Finset.sum_nbij' (fun p => (p.1.erase i, p.2)) (fun p => (insert i p.1, p.2))
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_filter, mem_product] at hp ⊢
      obtain ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩ := hp
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [mem_memberSubfamily, insert_erase hi1]; exact ⟨hS, notMem_erase _ _⟩
      · rw [mem_nonMemberSubfamily]; exact ⟨hT, hi2⟩
      · exact hd.mono_left (erase_subset _ _)
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_filter, mem_product] at hp ⊢
      obtain ⟨⟨hS, hT⟩, hd⟩ := hp
      rw [mem_memberSubfamily] at hS; rw [mem_nonMemberSubfamily] at hT
      obtain ⟨hSins, hiS⟩ := hS; obtain ⟨hTm, hiT⟩ := hT
      refine ⟨⟨⟨hSins, hTm⟩, ?_⟩, ?_, ?_⟩
      · rw [Finset.disjoint_insert_left]; exact ⟨hiT, hd⟩
      · exact mem_insert_self _ _
      · exact hiT
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_filter, mem_product] at hp
      obtain ⟨_, hi1, _⟩ := hp; simp only [insert_erase hi1]
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_filter, mem_product] at hp
      obtain ⟨⟨hS, _⟩, _⟩ := hp
      rw [mem_memberSubfamily] at hS; simp only [erase_insert hS.2]
    · rintro ⟨S, T⟩ hp
      simp only [Finset.mem_filter, mem_product] at hp
      obtain ⟨⟨_, hd⟩, hi1, hi2⟩ := hp
      rw [fwt_of_mem w hi1, fwt_of_notMem w hi2]; ring
  · apply Finset.filter_congr
    rintro ⟨S, T⟩ hp
    rw [mem_filter] at hp
    simp only [iff_self_and]
    intro hi1 hi2
    exact (Finset.disjoint_left.mp hp.2 hi1) hi2


theorem wfiber_notMem_mem (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    (∑ p ∈ (((𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2)).filter
              (fun p => i ∉ p.1 ∧ i ∈ p.2)), fwt w p.1 * fwt w p.2)
    = w i false * w i true * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
  classical
  unfold wdpairs'
  rw [Finset.mul_sum]
  apply Finset.sum_nbij' (fun p => (p.1, p.2.erase i)) (fun p => (p.1, insert i p.2))
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨⟨hS, hT⟩, hd⟩, hi1, hi2⟩ := hp
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_nonMemberSubfamily]; exact ⟨hS, hi1⟩
    · rw [mem_memberSubfamily, insert_erase hi2]; exact ⟨hT, notMem_erase _ _⟩
    · exact hd.mono_right (erase_subset _ _)
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp ⊢
    obtain ⟨⟨hS, hT⟩, hd⟩ := hp
    rw [mem_nonMemberSubfamily] at hS; rw [mem_memberSubfamily] at hT
    obtain ⟨hSm, hiS⟩ := hS; obtain ⟨hTins, hiT⟩ := hT
    refine ⟨⟨⟨hSm, hTins⟩, ?_⟩, ?_, ?_⟩
    · rw [Finset.disjoint_insert_right]; exact ⟨hiS, hd⟩
    · exact hiS
    · exact mem_insert_self _ _
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp
    obtain ⟨_, _, hi2⟩ := hp; simp only [insert_erase hi2]
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp
    obtain ⟨⟨_, hT⟩, _⟩ := hp
    rw [mem_memberSubfamily] at hT; simp only [erase_insert hT.2]
  · rintro ⟨S, T⟩ hp
    simp only [Finset.mem_filter, mem_product] at hp
    obtain ⟨⟨_, hd⟩, hi1, hi2⟩ := hp
    rw [fwt_of_notMem w hi1, fwt_of_mem w hi2]; ring


theorem wdpairs_fiber_recursion (w : α → Bool → ℝ) (𝒜 ℬ : Finset (Finset α)) (i : α) :
    wdpairs w 𝒜 ℬ
      = w i false * w i false * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
      + w i true * w i false * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
      + w i false * w i true * wdpairs' w i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i) := by
  classical
  unfold wdpairs
  set D := (𝒜 ×ˢ ℬ).filter (fun p => Disjoint p.1 p.2) with hD
  have hsplit1 :
      (∑ p ∈ D.filter (fun p => i ∈ p.1), fwt w p.1 * fwt w p.2)
        + (∑ p ∈ D.filter (fun p => i ∉ p.1), fwt w p.1 * fwt w p.2)
      = ∑ p ∈ D, fwt w p.1 * fwt w p.2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have hsplit2 :
      (∑ p ∈ (D.filter (fun p => i ∉ p.1)).filter (fun p => i ∈ p.2), fwt w p.1 * fwt w p.2)
        + (∑ p ∈ (D.filter (fun p => i ∉ p.1)).filter (fun p => i ∉ p.2), fwt w p.1 * fwt w p.2)
      = ∑ p ∈ D.filter (fun p => i ∉ p.1), fwt w p.1 * fwt w p.2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have e1 : (D.filter (fun p => i ∉ p.1)).filter (fun p => i ∈ p.2)
          = D.filter (fun p => i ∉ p.1 ∧ i ∈ p.2) := by rw [Finset.filter_filter]
  have e2 : (D.filter (fun p => i ∉ p.1)).filter (fun p => i ∉ p.2)
          = D.filter (fun p => i ∉ p.1 ∧ i ∉ p.2) := by rw [Finset.filter_filter]
  rw [e1, e2] at hsplit2
  rw [← hsplit1, ← hsplit2]
  rw [wfiber_mem_fst w 𝒜 ℬ i, wfiber_notMem_mem w 𝒜 ℬ i, wfiber_notMem_notMem w 𝒜 ℬ i]
  ring


theorem wdpairs_add_member_le_mul {w : α → Bool → ℝ} (hw : ∀ x b, 0 ≤ w x b)
    (𝒜 ℬ : Finset (Finset α)) (i : α) :
    wdpairs w 𝒜 ℬ
        + w i true * w i true
            * wdpairs' w i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
      ≤ fmarg w 𝒜 * fmarg w ℬ := by
  have hrec := wdpairs_fiber_recursion w 𝒜 ℬ i
  have hA := fmarg_split w 𝒜 i
  have hB := fmarg_split w ℬ i
  have hNN := wdpairs'_le_mul hw i (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)
  have hMN := wdpairs'_le_mul hw i (𝒜.memberSubfamily i) (ℬ.nonMemberSubfamily i)
  have hNM := wdpairs'_le_mul hw i (𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i)
  have hMM := wdpairs'_le_mul hw i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
  set w0 := w i false
  set w1 := w i true
  set Am := fmarg' w i (𝒜.memberSubfamily i)
  set An := fmarg' w i (𝒜.nonMemberSubfamily i)
  set Bm := fmarg' w i (ℬ.memberSubfamily i)
  set Bn := fmarg' w i (ℬ.nonMemberSubfamily i)
  have hw0 : 0 ≤ w0 := hw i false
  have hw1 : 0 ≤ w1 := hw i true
  have hMMnn := wdpairs'_nonneg hw i (𝒜.memberSubfamily i) (ℬ.memberSubfamily i)
  rw [hrec, hA, hB]
  nlinarith [hNN, hMN, hNM, hMM, hMMnn, mul_nonneg hw0 hw0, mul_nonneg hw1 hw0,
    mul_nonneg hw0 hw1, mul_nonneg hw1 hw1]

end Weighted
end StatMech
