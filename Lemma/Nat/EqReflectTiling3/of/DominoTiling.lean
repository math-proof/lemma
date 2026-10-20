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
  (T : DominoTiling n 3) :
-- imply
  reflectTiling3 (reflectTiling3 T) = T := by
-- proof
  exact DominoTilings.reflectTiling3_involutive T


-- created on 2026-10-20
