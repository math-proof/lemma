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
  (d : Domino) :
-- imply
  ¬(d.isHorizontal ∧ d.isVertical) := by
-- proof
  intro ⟨hH, hV⟩
  exact d.distinct (Prod.ext hV hH)


-- created on 2026-10-20
