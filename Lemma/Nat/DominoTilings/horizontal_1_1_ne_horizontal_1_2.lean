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
  horizontal_1_1 ≠ horizontal_1_2 := by
-- proof
  intro h
  have := congrArg Domino.cell1 h
  simp at this


-- created on 2026-10-20
