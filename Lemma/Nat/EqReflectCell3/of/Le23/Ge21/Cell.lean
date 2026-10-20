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
  (c : Cell)
  (h0 : c.2 ≥ 1)
  (h1 : c.2 ≤ 3) :
-- imply
  reflectCell3 (reflectCell3 c) = c := by
-- proof
  simp only [reflectCell3]
  ext <;> omega


-- created on 2026-10-20
