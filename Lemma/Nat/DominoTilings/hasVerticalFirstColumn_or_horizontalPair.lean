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
  (T : DominoTiling (n + 2) 2) :
-- imply
  hasVerticalFirstColumn T ∨
      (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset Cell)) ∧
      (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset Cell)) := by
-- proof
  obtain ⟨d, hd_mem, hd_cov⟩ := exists_domino_covering_11 T
  obtain hvert | hhoriz := domino_covering_11_cells T d hd_mem hd_cov
  ·
    left
    exact ⟨d, hd_mem, hvert⟩
  ·
    right
    constructor
    · exact ⟨d, hd_mem, hhoriz⟩
    ·
      obtain ⟨d', hd'_mem, hd'_ne, hd'_cov⟩ := exists_domino_covering_12_of_horizontal T d hd_mem hhoriz
      exact ⟨d', hd'_mem, domino_covering_12_cells T d d' hd_mem hd'_mem hd'_ne hhoriz hd'_cov⟩


-- created on 2026-10-20
