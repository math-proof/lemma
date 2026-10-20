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
  (T : DominoTiling n m) :
-- imply
  (Rectangle n m).card = 2 * T.dominos.card := by
-- proof
  rw [← T.covers_all]
  rw [Finset.card_biUnion]
  · have h : ∑ d ∈ T.dominos, d.cells.card = ∑ _d ∈ T.dominos, 2 := by
      apply Finset.sum_congr rfl
      intro d _
      exact Domino.card_cells d
    rw [h]
    simp [mul_comm]
  · intro d₁ hd₁ d₂ hd₂ hne
    exact T.pairwise_disjoint d₁ hd₁ d₂ hd₂ hne


-- created on 2026-10-20
