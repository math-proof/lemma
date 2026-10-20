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
  (T : DominoTiling (n + 2) 2)
  (hv_mem : vertical_1_1 ∈ T.dominos)
  (hv : hasVerticalFirstColumn T) :
-- imply
  Classical.choose hv = vertical_1_1 := by
-- proof
  have hspec := Classical.choose_spec hv
  -- The chosen domino has cells = vertical_1_1.cells, so it's either vertical_1_1 or vertical_1_1_flip
  rcases eq_vertical_1_1_of_cells_eq _ hspec.2 with heq | heq
  · exact heq
  · -- If it were vertical_1_1_flip, then vertical_1_1_flip ∈ T.dominos
    -- But vertical_1_1 ∈ T.dominos, so by disjointness, vertical_1_1_flip ∉ T.dominos
    exfalso
    rw [heq] at hspec
    exact vertical_1_1_flip_not_mem_of_vertical_1_1_mem T hv_mem hspec.1


-- created on 2026-10-20
