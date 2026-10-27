import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.Eq2.of.Ge1.NotHasVerticalInCol.IsFaultfree.DominoTiling
import Lemma.Nat.Even.AnyDominoTiling.of.IsFaultfree.DominoTiling
import Lemma.Nat.Even.AnyTilingEquiv.of.IsFaultfree.DominoTiling
import Lemma.Nat.HasTopVerticalInColOrHasBottomVerticalInCol.of.DominoTiling
import Lemma.Nat.TilingEquiv.of.NotHasVerticalInCol.IsFaultfree.DominoTiling
open DominoTilings
open Domino DominoTiling
open Finset
open Nat


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
    obtain htop | hbot := HasTopVerticalInColOrHasBottomVerticalInCol.of.DominoTiling n T hvert
    ·
      -- Top vertical case: T is some A_n
      left
      exact (Even.AnyTilingEquiv.of.IsFaultfree.DominoTiling n T hfree htop).2
    ·
      -- Bottom vertical case: T is some B_n
      right
      left
      exact (Even.AnyDominoTiling.of.IsFaultfree.DominoTiling n T hfree hbot).2
  ·
    -- No vertical domino in column 1: T is equivalent to C and n = 2
    intro hvert
    right
    right
    have hn2 : n = 2 := Eq2.of.Ge1.NotHasVerticalInCol.IsFaultfree.DominoTiling n T hfree hvert hn
    subst hn2
    exact ⟨rfl, hvert, rfl, TilingEquiv.of.NotHasVerticalInCol.IsFaultfree.DominoTiling T hvert hfree⟩


-- created on 2026-10-20
