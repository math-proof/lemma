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
  (n : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2) :
-- imply
  (TilingB n hn hn_ge).hasBottomVerticalInCol 1 := by
-- proof
  unfold DominoTiling.hasBottomVerticalInCol
  use leftWallB
  constructor
  · -- leftWallB ∈ (TilingB n hn hn_ge).dominos
    simp only [TilingB, Finset.mem_union, Finset.mem_singleton]
    left; left; left; right
    trivial
  · constructor
    · -- leftWallB.isVertical
      unfold Domino.isVertical
      simp [leftWallB]
    · constructor
      · -- leftWallB.cell1.1 = 1
        simp [leftWallB]
      · -- (leftWallB.cell1.2 = 1 ∧ leftWallB.cell2.2 = 2) ∨ (leftWallB.cell1.2 = 2 ∧ leftWallB.cell2.2 = 1)
        right
        simp [leftWallB]


-- created on 2026-10-20
