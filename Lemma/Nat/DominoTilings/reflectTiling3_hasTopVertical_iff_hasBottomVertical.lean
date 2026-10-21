import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
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
  {n : ℕ}
  (T : DominoTiling n 3)
  (c : ℕ) :
-- imply
  (reflectTiling3 T).hasTopVerticalInCol c ↔ T.hasBottomVerticalInCol c := by
-- proof
  constructor
  ·
    intro ⟨d, hd_mem, hd_vert, hd_col, hd_rows⟩
    simp only [reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
      ← Function.Embedding.toFun_eq_coe] at hd_mem
    obtain ⟨d', hd'_mem, rfl⟩ := hd_mem
    refine ⟨d', hd'_mem, ?_, ?_, ?_⟩
    ·
      simp only [Domino.isVertical] at hd_vert ⊢
      change (reflectCell3 d'.cell1).1 = (reflectCell3 d'.cell2).1 at hd_vert
      simpa [reflectCell3] using hd_vert
    ·
      change (reflectCell3 d'.cell1).1 = c at hd_col
      simpa [reflectCell3] using hd_col
    ·
      change ((reflectCell3 d'.cell1).2 = 2 ∧ (reflectCell3 d'.cell2).2 = 3) ∨
        ((reflectCell3 d'.cell1).2 = 3 ∧ (reflectCell3 d'.cell2).2 = 2) at hd_rows
      simp only [reflectCell3] at hd_rows
      obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := hd_rows
      ·
        right
        constructor <;> omega
      ·
        left
        constructor <;> omega
  ·
    intro ⟨d, hd_mem, hd_vert, hd_col, hd_rows⟩
    simp only [hasTopVerticalInCol, reflectTiling3, Finset.mem_map, Finset.mem_attach, true_and,
      Subtype.exists, ← Function.Embedding.toFun_eq_coe]
    refine ⟨_, ⟨d, hd_mem, rfl⟩, ?_, ?_, ?_⟩
    ·
      simp only [Domino.isVertical] at hd_vert ⊢
      change (reflectCell3 d.cell1).1 = (reflectCell3 d.cell2).1
      simpa [reflectCell3] using hd_vert
    ·
      change (reflectCell3 d.cell1).1 = c
      simpa [reflectCell3] using hd_col
    ·
      change ((reflectCell3 d.cell1).2 = 2 ∧ (reflectCell3 d.cell2).2 = 3) ∨
        ((reflectCell3 d.cell1).2 = 3 ∧ (reflectCell3 d.cell2).2 = 2)
      simp only [reflectCell3]
      obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := hd_rows
      ·
        right
        constructor <;> omega
      ·
        left
        constructor <;> omega


-- created on 2026-10-20
