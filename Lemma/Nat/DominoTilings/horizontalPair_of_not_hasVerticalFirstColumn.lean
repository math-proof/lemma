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
  (T : DominoTiling (n + 2) 2)
  (hnotvert : ¬hasVerticalFirstColumn T) :
-- imply
  (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset Cell)) ∧
      (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset Cell)) := by
-- proof
  obtain hvert | hhoriz := hasVerticalFirstColumn_or_horizontalPair T
  · exact absurd hvert hnotvert
  · exact hhoriz


-- created on 2026-10-20
