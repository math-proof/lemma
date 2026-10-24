import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
import Lemma.Nat.DominoTilings
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
  (TilingA n hn hn_ge).hasTopVerticalInCol 1 := by
-- proof
  -- We show that leftWall is in the dominos and satisfies the property
  use leftWall
  constructor
  ·
    -- leftWall ∈ dominos
    simp only [TilingA, Finset.mem_union, Finset.mem_singleton]
    left; left; left; right
    trivial
  ·
    -- leftWall.isVertical ∧ leftWall.cell1.1 = 1 ∧ ...
    constructor
    ·
      -- isVertical: cell1.1 = cell2.1 = 1
      rfl
    constructor
    ·
      -- cell1.1 = 1
      rfl
    ·
      -- rows condition: cell1.2 = 3 - 1 = 2 and cell2.2 = 3
      left
      constructor <;> rfl


-- created on 2026-10-20
