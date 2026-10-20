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
  Function.Injective (@tiling_2_from_sum n) :=
-- proof
  fun x y h => by
  have hx := tiling_2_to_sum_from_sum x
  have hy := tiling_2_to_sum_from_sum y
  rw [h] at hx
  exact hx.symm.trans hy


-- created on 2026-10-20
