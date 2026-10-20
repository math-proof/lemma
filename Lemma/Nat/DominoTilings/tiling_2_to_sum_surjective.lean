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
  Function.Surjective (@tiling_2_to_sum n) :=
-- proof
  fun x =>
  ⟨tiling_2_from_sum x, tiling_2_to_sum_from_sum x⟩


-- created on 2026-10-20
