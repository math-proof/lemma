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
  Xor d.isHorizontal d.isVertical := by
-- proof
  rcases d.isHorizontal_or_isVertical with hH | hV
  · exact Or.inl ⟨hH, fun hV => d.not_isHorizontal_and_isVertical ⟨hH, hV⟩⟩
  · exact Or.inr ⟨hV, fun hH => d.not_isHorizontal_and_isVertical ⟨hH, hV⟩⟩


-- created on 2026-10-20
