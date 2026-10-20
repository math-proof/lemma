import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (T : DominoTiling n 2)
  (d : Domino)
  (hd : d ∈ (prependVertical T).dominos)
  (hd_cells : d.cells = ({(1, 1), (1, 2)} : Finset Cell)) :
-- imply
  d = vertical_1_1 := by
-- proof
  simp only [prependVertical, Finset.mem_insert, Finset.mem_image] at hd
  obtain rfl | ⟨d', _, rfl⟩ := hd
  · rfl
  · -- d = d'.shiftNat 1, but shifted dominos have column ≥ 2
    have hcols := domino_cells_col_ge_one T d' (by assumption)
    simp only [Domino.cells, Domino.shiftNat_cell1, Domino.shiftNat_cell2] at hd_cells
    have h : (d'.cell1.1 + 1, d'.cell1.2) ∈ ({(1, 1), (1, 2)} : Finset Cell) := by
      rw [← hd_cells]; exact Finset.mem_insert_self _ _
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨h, _⟩ | ⟨h, _⟩ := h <;> omega


-- created on 2026-10-20
