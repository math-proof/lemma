import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset
set_option linter.unusedSimpArgs false


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : DominoTiling n 3)
  (htop : T.hasTopVerticalInCol 1)
  (hn : n ≥ 2) :
-- imply
  ∃ d ∈ T.dominos, d.cells = {(1, 1), (2, 1)} := by
-- proof
  have h11_in : (1, 1) ∈ Rectangle n 3 := by rw [mem_Rectangle]; omega
  obtain ⟨d, hd_mem, hd_cov⟩ := T.cell_covered (1, 1) h11_in
  obtain ⟨d_top, hd_top_mem, hd_top_vert, hd_top_col, hd_top_rows⟩ := htop
  have hd_in_rect := T.dominos_in_rect d hd_mem
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := hd_in_rect (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := hd_in_rect (by simp [Domino.cells])
  rw [mem_Rectangle] at hd_c1_in hd_c2_in
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hd_cov
  have hd_top_c2_col : d_top.cell2.1 = 1 := hd_top_vert.symm.trans hd_top_col
  have hd_top_covers_12 : (1, 2) ∈ d_top.cells := by
    simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
    obtain ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩ := hd_top_rows
    ·
      left
      ext
      exact hd_top_col.symm
      omega
    ·
      right
      ext
      exact hd_top_c2_col.symm
      omega
  have hd_ne_top : d ≠ d_top := by
    intro heq; subst heq
    obtain hc | hc := hd_cov
    ·
      rcases hd_top_rows with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
      ·
        have : (1 : ℕ) = 2 := by rw [← hc] at hr1
        exact hr1
        omega
      ·
        have : (1 : ℕ) = 3 := by rw [← hc] at hr1
        exact hr1
        omega
    ·
      rcases hd_top_rows with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
      ·
        have : (1 : ℕ) = 3 := by rw [← hc] at hr2
        exact hr2
        omega
      ·
        have : (1 : ℕ) = 2 := by rw [← hc] at hr2
        exact hr2
        omega
  have hd_not_12 : (1, 2) ∉ d.cells := by
    intro h12
    have := DominoTiling.cell_covered_unique T (1, 2) d d_top hd_mem hd_top_mem h12 hd_top_covers_12
    exact hd_ne_top this
  use d, hd_mem
  obtain hc1 | hc2 := hd_cov
  ·
    have hc1_eq : d.cell1 = (1, 1) := hc1.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    ·
      have hc2_col : d.cell2.1 = 1 := by rw [← hcol, hc1_eq]
      obtain h | h := hrow
      ·
        have hc2_eq : d.cell2 = (1, 2) := by ext
        exact hc2_col
        rw [hc1_eq] at h
        omega
        exfalso; apply hd_not_12; simp [Domino.cells, hc2_eq]
      ·
        have hc2_row : d.cell2.2 = 0 := by rw [hc1_eq] at h
        omega
        have hge1 : d.cell2.2 ≥ 1 := hd_c2_in.2.2.1
        omega
    ·
      have hc2_row : d.cell2.2 = 1 := by rw [← hrow, hc1_eq]
      obtain h | h := hcol
      ·
        have hc2_eq : d.cell2 = (2, 1) := by ext
        rw [hc1_eq] at h
        omega
        exact hc2_row
        simp only [Domino.cells, hc1_eq, hc2_eq]
      ·
        have hc2_col : d.cell2.1 = 0 := by rw [hc1_eq] at h
        omega
        have hge1 : d.cell2.1 ≥ 1 := hd_c2_in.1
        omega
  ·
    have hc2_eq : d.cell2 = (1, 1) := hc2.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    ·
      have hc1_col : d.cell1.1 = 1 := by rw [hcol, hc2_eq]
      obtain h | h := hrow
      ·
        have hc1_row : d.cell1.2 = 0 := by rw [hc2_eq] at h
        omega
        have hge1 : d.cell1.2 ≥ 1 := hd_c1_in.2.2.1
        omega
      ·
        have hc1_eq : d.cell1 = (1, 2) := by ext
        exact hc1_col
        rw [hc2_eq] at h
        omega
        exfalso; apply hd_not_12; simp [Domino.cells, hc1_eq]
    ·
      have hc1_row : d.cell1.2 = 1 := by rw [hrow, hc2_eq]
      obtain h | h := hcol
      ·
        have hc1_col : d.cell1.1 = 0 := by rw [hc2_eq] at h
        omega
        have hge1 : d.cell1.1 ≥ 1 := hd_c1_in.1
        omega
      ·
        have hc1_eq' : d.cell1 = (2, 1) := by ext
        rw [hc2_eq] at h
        omega
        exact hc1_row
        simp only [Domino.cells, hc1_eq', hc2_eq, Finset.pair_comm]


-- created on 2026-10-20
