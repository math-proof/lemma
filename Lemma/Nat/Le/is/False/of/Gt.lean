import Lemma.Bool.Iff_False.of.Not
import Lemma.Nat.NotLe.of.Gt
open Bool Nat


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a ≤ b ↔ False := by
-- proof
  have := NotLe.of.Gt h
  apply Iff_False.of.Not this


-- created on 2025-03-29
