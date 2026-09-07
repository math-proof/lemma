import Lemma.Finset.Card.of.Eq
import Lemma.Finset.CardUnion.eq.Add_CardSDiff
import Lemma.Finset.UnionDiff__Inter
open Finset


@[main]
private lemma main
  [DecidableEq α]
  {A B : Finset α} :
-- imply
  B.card = (A ∩ B).card + (B \ A).card :=
-- proof
  calc
    _ = ((B \ A) ∪ (B ∩ A)).card :=
      (Card.of.Eq (UnionDiff__Inter (s := B) (t := A))).symm
    _ = ((B \ A) \ (B ∩ A)).card + (B ∩ A).card :=
      CardUnion.eq.Add_CardSDiff (A := B \ A) (B := B ∩ A)
    _ = (B \ A).card + (A ∩ B).card := by
      rw [(by simp [disjoint_sdiff_inter] : (B \ A) \ (B ∩ A) = B \ A), inter_comm]
    _ = (A ∩ B).card + (B \ A).card := by
      rw [Nat.add_comm]


-- created on 2023-06-01
-- updated on 2026-09-07
