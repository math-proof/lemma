import Lemma.Nat.NotGe.of.Lt
import Lemma.Bool.Iff_False.of.Not
open Bool Nat


@[path]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a < b) :
-- imply
  a ≥ b ↔ False := by
-- proof
  have := NotGe.of.Lt h
  apply Iff_False.of.Not this


-- created on 2025-03-29
