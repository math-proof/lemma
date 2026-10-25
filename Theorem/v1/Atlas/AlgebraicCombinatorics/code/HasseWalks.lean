/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/HasseWalks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Young.YoungDiagram
import Mathlib.Data.Finset.Grade
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.Linarith
import Structure.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks


namespace HasseWalks

lemma isLowerSet_insert_minimal {μ ν : YoungDiagram}
    (m : ℕ × ℕ) (hm_ν : m ∈ ν.cells) (hm_nμ : m ∉ μ.cells)
    (h_below : ∀ c : ℕ × ℕ, c ∈ ν.cells → c.1 ≤ m.1 → c.2 ≤ m.2 → c ≠ m → c ∈ μ.cells) :
    IsLowerSet ((↑(Finset.cons m μ.cells hm_nμ)) : Set (ℕ × ℕ)) := by
  intro x y hle hx_mem
  have hx : x ∈ Finset.cons m μ.cells hm_nμ := hx_mem
  rw [Finset.mem_cons] at hx
  suffices y ∈ Finset.cons m μ.cells hm_nμ from this
  rcases hx with hx_eq | hx_μ
  · have hle' : y ≤ m := hx_eq ▸ hle
    by_cases hy_eq : y = m
    · rw [hy_eq]; exact Finset.mem_cons_self m μ.cells
    · exact Finset.mem_cons.mpr (Or.inr
        (h_below y (ν.isLowerSet hle' hm_ν) hle'.1 hle'.2 hy_eq))
  · exact Finset.mem_cons.mpr (Or.inr (μ.isLowerSet hle hx_μ))

theorem card_covBy_succ {μ ν : YoungDiagram} (h : μ ⋖ ν) :
    ν.card = μ.card + 1 := by
  have hsub : μ.cells ⊆ ν.cells := h.lt.le
  have hne : μ ≠ ν := ne_of_lt h.lt
  have hsdiff_nonempty : (ν.cells \ μ.cells).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
    exact fun hsub' => hne (le_antisymm h.lt.le hsub')
  suffices h1 : (ν.cells \ μ.cells).card = 1 by
    have h2 := Finset.card_sdiff_add_card_eq_card hsub
    simp only [YoungDiagram.card]; omega
  by_contra h_ne1
  exfalso
  have hcard_ge1 := hsdiff_nonempty.card_pos
  set sdiff := ν.cells \ μ.cells with sdiff_def
  have img_ne : (sdiff.image (fun p : ℕ × ℕ => p.1 + p.2)).Nonempty :=
    hsdiff_nonempty.image _
  obtain ⟨m, hm_sdiff, hm_eq⟩ : ∃ m ∈ sdiff, m.1 + m.2 =
      (sdiff.image (fun p : ℕ × ℕ => p.1 + p.2)).min' img_ne := by
    have := Finset.min'_mem _ img_ne
    rw [Finset.mem_image] at this
    obtain ⟨m, hm, hmeq⟩ := this
    exact ⟨m, hm, hmeq⟩
  have hm_ν := (Finset.mem_sdiff.mp hm_sdiff).1
  have hm_nμ := (Finset.mem_sdiff.mp hm_sdiff).2
  have h_min_le : ∀ c ∈ sdiff, m.1 + m.2 ≤ c.1 + c.2 := by
    intro c hc
    rw [hm_eq]
    exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)
  have h_below : ∀ c : ℕ × ℕ, c ∈ ν.cells → c.1 ≤ m.1 → c.2 ≤ m.2 → c ≠ m →
      c ∈ μ.cells := by
    intro c hc_ν hc1 hc2 hc_ne
    by_contra hc_nμ
    have hc_sdiff : c ∈ sdiff := Finset.mem_sdiff.mpr ⟨hc_ν, hc_nμ⟩
    have := h_min_le c hc_sdiff
    have hle12 : c.1 + c.2 ≤ m.1 + m.2 := Nat.add_le_add hc1 hc2
    have : c.1 = m.1 := le_antisymm hc1 (by omega)
    have : c.2 = m.2 := le_antisymm hc2 (by omega)
    exact hc_ne (Prod.ext ‹c.1 = m.1› ‹c.2 = m.2›)
  set ξ : YoungDiagram := ⟨Finset.cons m μ.cells hm_nμ,
    isLowerSet_insert_minimal m hm_ν hm_nμ h_below⟩
  have hμ_lt_ξ : μ < ξ := by
    rw [show (μ < ξ) = (μ.cells ⊂ ξ.cells) from rfl]
    exact Finset.ssubset_cons hm_nμ
  have hξ_lt_ν : ξ < ν := by
    rw [show (ξ < ν) = (ξ.cells ⊂ ν.cells) from rfl]
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [show ξ.cells = Finset.cons m μ.cells hm_nμ from rfl, Finset.mem_cons] at hx
      rcases hx with rfl | hx_μ
      · exact hm_ν
      · exact hsub hx_μ
    · intro h_eq
      have : ξ.cells.card = μ.cells.card + 1 := by
        rw [show ξ.cells = Finset.cons m μ.cells hm_nμ from rfl]
        exact Finset.card_cons hm_nμ
      have hν_card : ν.cells.card = μ.cells.card + 1 := by
        rw [← h_eq]; exact this
      have h_sdiff_card := Finset.card_sdiff_add_card_eq_card hsub
      rw [sdiff_def] at h_ne1 hcard_ge1
      omega
  exact (h.2 hμ_lt_ξ) hξ_lt_ν

end HasseWalks
