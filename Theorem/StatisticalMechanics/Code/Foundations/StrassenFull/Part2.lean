/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Def.StatisticalMechanics.Code.Foundations.StrassenFull
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Transport

open Filter Topology


variable {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]


theorem layer_cake [Nonempty P] (g : P → ℝ) (h : P → ℝ) (hanti : Antitone h)
    (hpos : ∀ x, 0 ≤ h x) (hg : ∀ D : Finset P, IsDown D → 0 ≤ ∑ x ∈ D, g x) :
    0 ≤ ∑ x, g x * h x := by
  generalize hk : (univ.image h).card = k
  induction k using Nat.strong_induction_on generalizing h with
  | _ k IH =>
    by_cases hconst : ∃ c, ∀ x, h x = c
    · obtain ⟨c, hc⟩ := hconst
      have hcpos : 0 ≤ c := by rw [← hc (Classical.arbitrary P)]; exact hpos _
      calc 0 ≤ c * ∑ x, g x := by
              apply mul_nonneg hcpos
              simpa using hg univ (fun x y _ _ => mem_univ x)
        _ = ∑ x, g x * h x := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun x _ => by rw [hc x]; ring)
    · have himg_ne : (univ.image h).Nonempty := univ_nonempty.image h
      set M := (univ.image h).max' himg_ne with hMdef
      have hMmem : M ∈ univ.image h := Finset.max'_mem _ _
      have hMmax : ∀ x, h x ≤ M := fun x =>
        Finset.le_max' _ (h x) (mem_image_of_mem h (mem_univ x))
      set below := (univ.image h).filter (· < M) with hbelowdef
      have hbelow_ne : below.Nonempty := by
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        apply hconst
        refine ⟨M, fun x => le_antisymm (hMmax x) ?_⟩
        by_contra hlt
        rw [not_le] at hlt
        have hmem' : h x ∈ below := by
          rw [hbelowdef]; simp only [mem_filter, mem_image, mem_univ, true_and]
          exact ⟨⟨x, rfl⟩, hlt⟩
        rw [hempty] at hmem'; exact absurd hmem' (Finset.notMem_empty _)
      set mp := below.max' hbelow_ne with hmpdef
      have hmp_below : mp ∈ below := Finset.max'_mem _ _
      have hmpM : mp < M := by
        have := hmp_below; rw [hbelowdef] at this
        simp only [mem_filter] at this; exact this.2
      have hmpimg : mp ∈ univ.image h := by
        have := hmp_below; rw [hbelowdef] at this
        simp only [mem_filter] at this; exact this.1
      have hbelowle : ∀ x, h x < M → h x ≤ mp := by
        intro x hx
        apply Finset.le_max'
        rw [hbelowdef]; simp only [mem_filter, mem_image, mem_univ, true_and]
        exact ⟨⟨x, rfl⟩, hx⟩
      have hsplit : ∀ x, h x = M ∨ h x ≤ mp := by
        intro x; rcases eq_or_lt_of_le (hMmax x) with he | hl
        · exact Or.inl he
        · exact Or.inr (hbelowle x hl)
      set h' := fun x => min (h x) mp with hh'def
      have hh'anti : Antitone h' := fun x y hxy => min_le_min (hanti hxy) (le_refl mp)
      have hmppos : 0 ≤ mp := by
        obtain ⟨x, hx⟩ : ∃ x, h x = mp := by simpa using hmpimg
        rw [← hx]; exact hpos x
      have hh'pos : ∀ x, 0 ≤ h' x := fun x => le_min (hpos x) hmppos
      set D := univ.filter (fun x => M ≤ h x) with hDdef
      have hDdown : IsDown D := by
        intro x y hxy hy
        rw [hDdef] at *; simp only [mem_filter, mem_univ, true_and] at *
        exact le_trans hy (hanti hxy)
      have hdecomp : ∑ x, g x * h x = (∑ x, g x * h' x) + (M - mp) * ∑ x ∈ D, g x := by
        have ptwise : ∀ x, g x * h x = g x * h' x + (if M ≤ h x then (M - mp) * g x else 0) := by
          intro x
          rcases hsplit x with hx | hx
          · simp only [hh'def, hx]; simp only [le_refl, if_pos]
            rw [min_eq_right (le_of_lt hmpM)]; ring
          · rw [hh'def]; simp only; rw [min_eq_left hx]
            by_cases hMx : M ≤ h x
            · have hxM : h x = M := le_antisymm (le_trans hx (le_of_lt hmpM)) hMx
              have hmpeqM : mp = M := le_antisymm (le_of_lt hmpM) (hxM ▸ hx)
              rw [if_pos hMx, hmpeqM]; ring
            · rw [if_neg hMx]; ring
        rw [Finset.sum_congr rfl (fun x _ => ptwise x), Finset.sum_add_distrib]
        congr 1
        rw [hDdef, Finset.mul_sum, ← Finset.sum_filter]
      rw [hdecomp]
      apply add_nonneg
      · apply IH ((univ.image h').card) ?_ h' hh'anti hh'pos rfl
        rw [← hk]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨M, hMmem, ?_⟩
          simp only [mem_image, not_exists, mem_univ, true_and, hh'def]
          intro x hcontra
          have hle : min (h x) mp ≤ mp := min_le_right _ _
          rw [hcontra] at hle; linarith
        · intro v hv
          simp only [mem_image, mem_univ, true_and, hh'def] at hv ⊢
          obtain ⟨x, rfl⟩ := hv
          rcases le_or_gt (h x) mp with hle | hlt
          · exact ⟨x, by rw [min_eq_left hle]⟩
          · rw [min_eq_right (le_of_lt hlt)]; simpa using hmpimg
      · exact mul_nonneg (by linarith) (hg D hDdown)


variable [DecidableRel ((· ≤ ·) : P → P → Prop)]


theorem dual_feasibility [Nonempty P] (μ ν : P → ℝ)
    (hμpos : ∀ x, 0 ≤ μ x) (hνpos : ∀ x, 0 ≤ ν x)
    (hTOT : ∑ x, μ x = ∑ x, ν x)
    (hDOM : ∀ D : Finset P, IsDown D → ∑ x ∈ D, ν x ≤ ∑ x ∈ D, μ x)
    (φ ψ : P → ℝ) (hfeas : ∀ x y, x ≤ y → 0 ≤ φ x + ψ y) :
    0 ≤ (∑ x, μ x * φ x) + ∑ y, ν y * ψ y := by
  have hne : ∀ x : P, (univ.filter (x ≤ ·)).Nonempty := fun x => ⟨x, by simp⟩
  set h : P → ℝ := fun x => (univ.filter (x ≤ ·)).sup' (hne x) (fun y => -ψ y) with hhdef
  have hge : ∀ x, -ψ x ≤ h x := fun x => Finset.le_sup' (f := fun y => -ψ y) (by simp)
  have hφh : ∀ x, h x ≤ φ x := by
    intro x; apply Finset.sup'_le
    intro y hy; simp only [mem_filter, mem_univ, true_and] at hy
    linarith [hfeas x y hy]
  have hanti : Antitone h := by
    intro x x' hxx'
    apply Finset.sup'_le
    intro y hy; simp only [mem_filter, mem_univ, true_and] at hy
    exact Finset.le_sup' (f := fun y => -ψ y) (by
      simp only [mem_filter, mem_univ, true_and]; exact le_trans hxx' hy)
  set c : ℝ := - (univ.inf' univ_nonempty h) with hcdef
  have hshiftpos : ∀ x, 0 ≤ h x + c := by
    intro x; rw [hcdef]
    have : univ.inf' univ_nonempty h ≤ h x := Finset.inf'_le _ (mem_univ x)
    linarith
  have hshiftanti : Antitone (fun x => h x + c) := fun x y hxy => by
    simp only; have := hanti hxy; linarith
  have key : 0 ≤ ∑ x, (μ x - ν x) * (h x + c) := by
    apply layer_cake (fun x => μ x - ν x) (fun x => h x + c) hshiftanti hshiftpos
    intro D hD
    rw [Finset.sum_sub_distrib]
    linarith [hDOM D hD]
  have hsum0 : ∑ x, (μ x - ν x) = 0 := by rw [Finset.sum_sub_distrib, hTOT, sub_self]
  have expand : ∑ x, (μ x - ν x) * (h x + c) = ∑ x, (μ x - ν x) * h x := by
    have hpt : ∀ x, (μ x - ν x) * (h x + c) = (μ x - ν x) * h x + c * (μ x - ν x) :=
      fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib, ← Finset.mul_sum,
      hsum0, mul_zero, add_zero]
  rw [expand] at key
  have step1 : (∑ x, (μ x - ν x) * h x) ≤ (∑ x, μ x * φ x) + ∑ y, ν y * ψ y := by
    rw [show (∑ x, (μ x - ν x) * h x) = (∑ x, μ x * h x) - ∑ x, ν x * h x by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun x _ => by ring)]
    have hA : (∑ x, μ x * h x) ≤ ∑ x, μ x * φ x :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hφh x) (hμpos x))
    have hB : -(∑ x, ν x * h x) ≤ ∑ y, ν y * ψ y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum; intro x _
      have hrw : -(ν x * h x) = ν x * (-h x) := by ring
      rw [hrw]; exact mul_le_mul_of_nonneg_left (by linarith [hge x]) (hνpos x)
    linarith
  linarith


end Transport
end StatMech
