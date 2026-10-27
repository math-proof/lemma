import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
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
  (n : ℕ)
  (d : Domino)
  (h_in : d.cells ⊆ Rectangle n 3)
  (h_cov : (n, 1) ∈ d.cells) :
-- imply
  d.cells = {(n - 1, 1), (n, 1)} ∨ d.cells = {(n, 1), (n, 2)} := by
-- proof
  simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at h_cov
  obtain hc1 | hc2 := h_cov
  · have h2_in : d.cell2 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
    rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at h2_in
    have hc1_col : d.cell1.1 = n := by rw [← hc1]
    have hc1_row : d.cell1.2 = 1 := by rw [← hc1]
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · right; simp only [Domino.cells]
      have hc2_col : d.cell2.1 = n := by rw [← hcol, hc1_col]
      obtain hr | hr := hrow
      · have hc2_row : d.cell2.2 = 2 := by omega
        have h2_eq : d.cell2 = (n, 2) := Prod.ext hc2_col hc2_row
        rw [← hc1, h2_eq]
      · exfalso; omega
    · left; simp only [Domino.cells]
      have hc2_row : d.cell2.2 = 1 := by rw [← hrow, hc1_row]
      obtain hc | hc := hcol
      · exfalso; omega
      · have hc2_col : d.cell2.1 = n - 1 := by omega
        have h2_eq : d.cell2 = (n - 1, 1) := Prod.ext hc2_col hc2_row
        rw [← hc1, h2_eq, Finset.pair_comm]
  · have h1_in : d.cell1 ∈ Rectangle n 3 := h_in (by simp [Domino.cells])
    rw [IffIn_RectangleGe1AndGe_1AndGe21AndGe_2] at h1_in
    have hc2_col : d.cell2.1 = n := by rw [← hc2]
    have hc2_row : d.cell2.2 = 1 := by rw [← hc2]
    obtain ⟨hcol, hrow⟩ | ⟨hrow, hcol⟩ := d.adjacent
    · right; simp only [Domino.cells]
      have hc1_col : d.cell1.1 = n := by rw [hcol, hc2_col]
      obtain hr | hr := hrow
      · exfalso; omega
      · have hc1_row : d.cell1.2 = 2 := by omega
        have h1_eq : d.cell1 = (n, 2) := Prod.ext hc1_col hc1_row
        rw [← hc2, h1_eq, Finset.pair_comm]
    · left; simp only [Domino.cells]
      have hc1_row : d.cell1.2 = 1 := by rw [hrow, hc2_row]
      obtain hc | hc := hcol
      · have hc1_col : d.cell1.1 = n - 1 := by omega
        have h1_eq : d.cell1 = (n - 1, 1) := Prod.ext hc1_col hc1_row
        rw [← hc2, h1_eq]
      · exfalso; omega


-- created on 2026-10-20
