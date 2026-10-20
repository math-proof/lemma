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
  d.isVertical ↔ ¬d.isHorizontal := by
-- proof
  constructor
  · intro hV hH
    exact d.not_isHorizontal_and_isVertical ⟨hH, hV⟩
  · intro hNH
    rcases d.isHorizontal_or_isVertical with hH | hV
    · exact absurd hH hNH
    · exact hV


-- created on 2026-10-20
