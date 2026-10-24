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
  (n : ℕ) :
-- imply
  Nonempty (DominoTiling n 3) → Even n ∨ n = 0 := by
-- proof
  intro ⟨T⟩ -- Rectangle n 3 has 3n cells, each domino covers 2 cells -- Since dominos partition the rectangle, 3n must be even -- Since 3 is odd, n must be even
  have h_disjoint : (T.dominos : Set Domino).PairwiseDisjoint Domino.cells := by
    intro d₁ hd₁ d₂ hd₂ hne
    exact T.pairwise_disjoint d₁ hd₁ d₂ hd₂ hne
  have h_sum : (T.dominos.biUnion Domino.cells).card = T.dominos.sum (fun d => d.cells.card) :=
    card_biUnion h_disjoint
  have h_cells_card : ∀ d : Domino, d.cells.card = 2 := fun d =>
    card_pair d.distinct
  have h_sum_two : T.dominos.sum (fun d => d.cells.card) = 2 * T.dominos.card := by
    simp only [h_cells_card, sum_const, smul_eq_mul, mul_comm]
  have h_rect_card : (Rectangle n 3).card = n * 3 := by
    simp only [Rectangle, card_map, card_product, card_range]
  have h_even_3n : Even (n * 3) := by
    rw [T.covers_all, h_rect_card] at h_sum
    rw [h_sum_two] at h_sum
    rw [h_sum]
    exact even_two_mul _
  obtain hn | hn := Nat.eq_zero_or_pos n
  · exact Or.inr hn
  ·
    left
    rw [Nat.even_mul] at h_even_3n
    exact h_even_3n.resolve_right (by decide)


-- created on 2026-10-20
