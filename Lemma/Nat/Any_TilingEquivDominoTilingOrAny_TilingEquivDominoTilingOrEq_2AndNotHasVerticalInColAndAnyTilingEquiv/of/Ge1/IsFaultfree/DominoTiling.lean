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
  (T : DominoTiling n 3)
  (hfree : T.isFaultfree)
  (hn : n ≥ 1) :
-- imply
  (∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingA n hn hn_ge)) ∨
      (∃ (hn : Even n) (hn_ge : n ≥ 2), DominoTiling.TilingEquiv T (TilingB n hn hn_ge)) ∨
      (n = 2 ∧ ¬T.hasVerticalInCol 1 ∧ ∃ h : n = 2,
        DominoTiling.TilingEquiv (h ▸ T) TilingC) := by
-- proof
  apply (Classical.em (T.hasVerticalInCol 1)).elim
  ·
    -- There is a vertical domino in column 1
    intro hvert
    obtain htop | hbot := vertical_in_col1_trichotomy n T hvert
    ·
      -- Top vertical case: T is some A_n
      left
      exact (faultfree_top_vertical_classification n T hfree htop).2
    ·
      -- Bottom vertical case: T is some B_n
      right
      left
      exact (faultfree_bottom_vertical_classification n T hfree hbot).2
  ·
    -- No vertical domino in column 1: T is equivalent to C and n = 2
    intro hvert
    right
    right
    have hn2 : n = 2 := no_vertical_implies_n_eq_2 n T hfree hvert hn
    subst hn2
    exact ⟨rfl, hvert, rfl, faultfree_no_vertical_unique T hfree hvert⟩


-- created on 2026-10-20
