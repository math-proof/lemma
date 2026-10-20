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
  exact DominoTilings.reflectTiling3_hasTopVertical_iff_hasBottomVertical T c


-- created on 2026-10-20
