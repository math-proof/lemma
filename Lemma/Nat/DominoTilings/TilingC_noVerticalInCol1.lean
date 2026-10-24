import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
open DominoTilings
open Domino DominoTiling
open Finset


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main :
-- imply
  ¬TilingC.hasVerticalInCol 1 := by
-- proof
  simp only [DominoTiling.hasVerticalInCol, TilingC, Finset.mem_insert, Finset.mem_singleton,
    Domino.isVertical]
  intro ⟨d, hd_mem, hd_vert, hd_col⟩
  obtain rfl | rfl | rfl := hd_mem <;> simp_all


-- created on 2026-10-20
