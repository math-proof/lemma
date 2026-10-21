import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.IffIn_RectangleGe1AndGe_1AndGe21AndGe_2
open DominoTilings
open Domino DominoTiling
open Finset
open Nat


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (n c : ℕ)
  (d : Domino)
  (_ : c ≥ 1)
  (_ : c < n)
  (h_in : d.cells ⊆ Rectangle n 3)
  (h_cov : (c, 2) ∈ d.cells)
  (h_not_left : (c - 1, 2) ∉ d.cells) :
-- imply
  d.cells = {(c, 2), (c + 1, 2)} ∨ d.cells = {(c, 1), (c, 2)} ∨ d.cells = {(c, 2), (c, 3)} := by
-- proof
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov h_not_left ⊢
  have hd_c1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  have hd_c2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
  rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at hd_c1_in hd_c2_in
  obtain hc1 | hc2 := h_cov
  · have hc1_eq : d.cell1 = (c, 2) := hc1.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · have hc2_col : d.cell2.1 = c := by rw [← hcol, hc1_eq]
      obtain h | h := hrow
      · have hc2_eq : d.cell2 = (c, 3) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; right; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (c, 1) := by ext; exact hc2_col; rw [hc1_eq] at h; omega
        right; left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc2_row : d.cell2.2 = 2 := by rw [← hrow, hc1_eq]
      obtain h | h := hcol
      · have hc2_eq : d.cell2 = (c + 1, 2) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        left; simp only [hc1_eq, hc2_eq]
      · have hc2_eq : d.cell2 = (c - 1, 2) := by ext; rw [hc1_eq] at h; omega; exact hc2_row
        exfalso; apply h_not_left; right; exact hc2_eq.symm
  · have hc2_eq : d.cell2 = (c, 2) := hc2.symm
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · have hc1_col : d.cell1.1 = c := by rw [hcol, hc2_eq]
      obtain h | h := hrow
      · have hc1_eq : d.cell1 = (c, 1) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; left; simp only [hc1_eq, hc2_eq]
      · have hc1_eq : d.cell1 = (c, 3) := by ext; exact hc1_col; rw [hc2_eq] at h; omega
        right; right; simp only [hc1_eq, hc2_eq, Finset.pair_comm]
    · have hc1_row : d.cell1.2 = 2 := by rw [hrow, hc2_eq]
      obtain h | h := hcol
      · have hc1_eq : d.cell1 = (c - 1, 2) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        exfalso; apply h_not_left; left; exact hc1_eq.symm
      · have hc1_eq : d.cell1 = (c + 1, 2) := by ext; rw [hc2_eq] at h; omega; exact hc1_row
        left; simp only [hc1_eq, hc2_eq, Finset.pair_comm]


-- created on 2026-10-20
