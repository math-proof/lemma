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
  (n : ℕ)
  (T : DominoTiling n 3)
  (c : ℕ)
  (htop : T.hasTopVerticalInCol c) :
-- imply
  n ≥ c := by
-- proof
  obtain ⟨d, hd_mem, hd_vert, hd_col, hd_rows⟩ := htop
  have h := T.dominos_in_rect d hd_mem
  have hcell1 : d.cell1 ∈ d.cells := by simp [Domino.cells]
  have hcell1_rect : d.cell1 ∈ Rectangle n 3 := h hcell1
  simp only [Rectangle, Finset.mem_map, Finset.mem_product, Finset.mem_range,
             ← Function.Embedding.toFun_eq_coe] at hcell1_rect
  obtain ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩ := hcell1_rect
  have hcell1_fst : d.cell1.1 = x + 1 := by
    have : (x + 1, y + 1) = d.cell1 := hxy
    rw [← this]
  rw [hd_col] at hcell1_fst
  omega


-- created on 2026-10-20
