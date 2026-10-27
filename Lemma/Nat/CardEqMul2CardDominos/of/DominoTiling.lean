import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.CardEq2.of.Domino
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
  (T : DominoTiling n m) :
-- imply
  (Rectangle n m).card = 2 * T.dominos.card := by
-- proof
  rw [← T.covers_all]
  rw [Finset.card_biUnion]
  ·
    have h : ∑ d ∈ T.dominos, d.cells.card = ∑ _ ∈ T.dominos, 2 := by
      apply Finset.sum_congr rfl
      intro d _
      exact CardEq2.of.Domino d
    rw [h]
    simp [mul_comm]
  ·
    intro d₁ hd₁ d₂ hd₂ hne
    exact T.pairwise_disjoint d₁ hd₁ d₂ hd₂ hne


-- created on 2026-10-20
