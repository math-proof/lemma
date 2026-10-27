import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (n : ℕ)
  (T : DominoTiling n 3) :
-- imply
  T.hasVerticalInCol 1 → T.hasTopVerticalInCol 1 ∨ T.hasBottomVerticalInCol 1 := by
-- proof
  intro ⟨d, hd_mem, hd_vert, hd_col⟩
  -- d is a vertical domino in column 1
  -- Both cells of d are in the rectangle R_{n,3}
  have hd_in_rect := T.dominos_in_rect d hd_mem
  have hcell1 : d.cell1 ∈ Rectangle n 3 := hd_in_rect (Finset.mem_insert_self _ _)
  have hcell2 : d.cell2 ∈ Rectangle n 3 :=
    hd_in_rect (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  -- Get row bounds from rectangle membership
  simp only [Rectangle, Finset.mem_map, ← Function.Embedding.toFun_eq_coe, Finset.mem_product,
    Finset.mem_range, Prod.exists] at hcell1 hcell2
  obtain ⟨x1, y1, ⟨_, hy1⟩, heq1⟩ := hcell1
  obtain ⟨x2, y2, ⟨_, hy2⟩, heq2⟩ := hcell2
  -- From heq1, heq2: d.cell1 = (x1+1, y1+1), d.cell2 = (x2+1, y2+1)
  -- So row bounds: 1 ≤ d.cell1.2 = y1+1 ≤ 3, 1 ≤ d.cell2.2 = y2+1 ≤ 3
  have h1_row_ge : 1 ≤ d.cell1.2 := by rw [← heq1]; omega
  have h1_row_le : d.cell1.2 ≤ 3 := by rw [← heq1]; omega
  have h2_row_ge : 1 ≤ d.cell2.2 := by rw [← heq2]; omega
  have h2_row_le : d.cell2.2 ≤ 3 := by rw [← heq2]; omega
  -- Since d is vertical, from adjacent property we have row relationship
  have hadj := d.adjacent
  obtain ⟨_, hrow_rel⟩ | ⟨_, hcol_rel⟩ := hadj
  · -- Vertical case: same column, adjacent rows
    obtain h1 | h2 := hrow_rel
    · -- cell1.2 + 1 = cell2.2: rows are (r, r+1) for some r
      -- With bounds 1 ≤ row ≤ 3, we have r ∈ {1, 2}
      have : d.cell1.2 = 1 ∨ d.cell1.2 = 2 := by omega
      obtain h | h := this
      · -- rows 1 and 2: bottom vertical
        right
        exact ⟨d, hd_mem, hd_vert, hd_col, Or.inl ⟨h, by omega⟩⟩
      · -- rows 2 and 3: top vertical
        left
        exact ⟨d, hd_mem, hd_vert, hd_col, Or.inl ⟨by omega, by omega⟩⟩
    · -- cell2.2 + 1 = cell1.2
      have : d.cell2.2 = 1 ∨ d.cell2.2 = 2 := by omega
      obtain h | h := this
      · -- rows 2 and 1: bottom vertical
        right
        exact ⟨d, hd_mem, hd_vert, hd_col, Or.inr ⟨by omega, h⟩⟩
      · -- rows 3 and 2: top vertical
        left
        exact ⟨d, hd_mem, hd_vert, hd_col, Or.inr ⟨by omega, by omega⟩⟩
  · -- Horizontal case: same row, adjacent columns
    -- But d is vertical, so cell1.1 = cell2.1
    -- This contradicts being horizontal (adjacent columns)
    exfalso
    unfold Domino.isVertical at hd_vert
    obtain h | h := hcol_rel <;> omega


-- created on 2026-10-20
