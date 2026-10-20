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
  {n : ℕ}
-- given
  (T : DominoTiling n 3)
  (c : ℕ) :
-- imply
  (reflectTiling3 T).hasTopVerticalInCol c ↔ T.hasBottomVerticalInCol c := by
-- proof
  constructor
  ·
    -- (→) If reflectTiling3 T has top vertical in column c, then T has bottom vertical in column c
    intro ⟨d, hd_mem, hd_vert, hd_col, hd_rows⟩
    -- d is in (reflectTiling3 T).dominos, so d = reflectDomino3 d' for some d' ∈ T.dominos
    simp only [reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      ← Function.Embedding.toFun_eq_coe] at hd_mem
    obtain ⟨d', hd'_mem, rfl⟩ := hd_mem
    -- Show d' is vertical and in the bottom rows
    use d', hd'_mem
    constructor
    ·
      -- d' is vertical: d'.cell1.1 = d'.cell2.1
      simp only [reflectDomino3, reflectCell3, Domino.isVertical] at hd_vert
      exact hd_vert
    constructor
    ·
      -- d'.cell1.1 = c
      simp only [reflectDomino3, reflectCell3] at hd_col
      exact hd_col
    ·
      -- d' is in bottom rows: reflectCell3 maps row y to 4-y, so 1↔3, 2↔2
      simp only [reflectDomino3, reflectCell3] at hd_rows
      obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_rows
      ·
        right
        constructor <;> omega
      ·
        left
        constructor <;> omega
  ·
    -- (←) If T has bottom vertical in column c, then reflectTiling3 T has top vertical in column c
    intro ⟨d, hd_mem, hd_vert, hd_col, hd_rows⟩
    -- The reflected domino is in reflectTiling3 T
    let d' := reflectDomino3 d (domino_cell1_row_le' (T.dominos_in_rect d hd_mem))
      (domino_cell2_row_le' (T.dominos_in_rect d hd_mem))
    use d'
    constructor
    ·
      -- d' ∈ (reflectTiling3 T).dominos
      simp only [reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe]
      exact ⟨d, hd_mem, rfl⟩
    constructor
    ·
      -- d' is vertical
      simp only [d', reflectDomino3, reflectCell3, Domino.isVertical]
      exact hd_vert
    constructor
    ·
      -- d'.cell1.1 = c
      simp only [d', reflectDomino3, reflectCell3]
      exact hd_col
    ·
      -- d' is in top rows (rows 2,3): bottom rows (1,2) or (2,1) map to (3,2) or (2,3)
      simp only [d', reflectDomino3, reflectCell3]
      obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := hd_rows
      ·
        right
        constructor <;> omega
      ·
        left
        constructor <;> omega


-- created on 2026-10-20
