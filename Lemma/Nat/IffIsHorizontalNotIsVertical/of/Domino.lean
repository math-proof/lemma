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
  d.isHorizontal ↔ ¬d.isVertical := by
-- proof
  constructor
  ·
    intro hH hV
    exact d.not_isHorizontal_and_isVertical ⟨hH, hV⟩
  ·
    intro hNV
    obtain hH | hV := d.isHorizontal_or_isVertical
    · exact hH
    · exact absurd hV hNV


-- created on 2026-10-20
