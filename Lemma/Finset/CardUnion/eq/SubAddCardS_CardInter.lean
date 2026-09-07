import Lemma.Finset.Card.eq.Add_CardSDiff
import Lemma.Finset.CardUnion.eq.Add_CardSDiff
open Finset


@[main]
private lemma main
  [DecidableEq α]
  {A B : Finset α} :
-- imply
  (A ∪ B).card = A.card + B.card - (A ∩ B).card := calc
-- proof
  _ = (B \ A).card + A.card := by
    rw [union_comm]
    apply CardUnion.eq.Add_CardSDiff
  _ = A.card + B.card - (A ∩ B).card := by
    have h := Card.eq.Add_CardSDiff (A := A) (B := B)
    have hle : (A ∩ B).card ≤ B.card := by
      rw [h]
      exact Nat.le_add_right _ _
    have : (B \ A).card = B.card - (A ∩ B).card := by
      rw [h, Nat.add_comm, Nat.add_sub_cancel]
    rw [this, Nat.add_comm (_ - _), ← Nat.add_sub_assoc hle]


-- created on 2020-07-06
-- updated on 2026-09-07
