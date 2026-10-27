import Mathlib
import Def.Combinatorics.Tiling.DominoTilings.Part11
open Finset BigOperators


namespace DominoTilings

theorem nat_sub_inj_4 {a b : ℕ} (ha : a ≤ 4) (hb : b ≤ 4) (h : 4 - a = 4 - b) : a = b := by
  omega


theorem domino_cell1_row_le' {n : ℕ} {d : Domino} (hd : d.cells ⊆ Rectangle n 3) :
    d.cell1.2 ≤ 3 := by
  have h : d.cell1 ∈ d.cells := by simp [Domino.cells]
  have h' := hd h
  rw [mem_Rectangle] at h'
  exact h'.2.2.2


theorem domino_cell2_row_le' {n : ℕ} {d : Domino} (hd : d.cells ⊆ Rectangle n 3) :
    d.cell2.2 ≤ 3 := by
  have h : d.cell2 ∈ d.cells := by simp [Domino.cells]
  have h' := hd h
  rw [mem_Rectangle] at h'
  exact h'.2.2.2


end DominoTilings
