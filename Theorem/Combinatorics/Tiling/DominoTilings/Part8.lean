import Mathlib
import Instance.Combinatorics.Tiling.DominoTilings.Part3
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


theorem hasVerticalFirstColumn_or_horizontalPair (T : DominoTiling (n + 2) 2) :
    hasVerticalFirstColumn T ∨
    (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset Cell)) ∧
    (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset Cell)) := by
  obtain ⟨d, hd_mem, hd_cov⟩ := exists_domino_covering_11 T
  rcases domino_covering_11_cells T d hd_mem hd_cov with hvert | hhoriz
  · left
    exact ⟨d, hd_mem, hvert⟩
  · right
    constructor
    · exact ⟨d, hd_mem, hhoriz⟩
    · obtain ⟨d', hd'_mem, hd'_ne, hd'_cov⟩ := exists_domino_covering_12_of_horizontal T d hd_mem hhoriz
      exact ⟨d', hd'_mem, domino_covering_12_cells T d d' hd_mem hd'_mem hd'_ne hhoriz hd'_cov⟩


theorem horizontalPair_of_not_hasVerticalFirstColumn (T : DominoTiling (n + 2) 2)
    (hnotvert : ¬hasVerticalFirstColumn T) :
    (∃ d₁ ∈ T.dominos, d₁.cells = ({(1, 1), (2, 1)} : Finset Cell)) ∧
    (∃ d₂ ∈ T.dominos, d₂.cells = ({(1, 2), (2, 2)} : Finset Cell)) := by
  rcases hasVerticalFirstColumn_or_horizontalPair T with hvert | hhoriz
  · exact absurd hvert hnotvert
  · exact hhoriz


end DominoTiling
end DominoTilings
