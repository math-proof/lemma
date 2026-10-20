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
  (x y : ℕ) :
-- imply
  (mkHorizontalDomino x y).cell1 = (x, y) :=
-- proof
  rfl


-- created on 2026-10-20
