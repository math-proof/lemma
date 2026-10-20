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
private lemma main :
-- imply
  vertical_1_1_flip.cells = vertical_1_1.cells := by
-- proof
  simp only [vertical_1_1_flip_cells, vertical_1_1_cells, Finset.pair_comm]


-- created on 2026-10-20
