import Lemma.Nat.Ge.of.Gt
open Nat


@[main]
private lemma main
  [LinearOrder α]
  {a b : α}
-- given
  (h : a > b) :
-- imply
  a ⊓ b = b := by
-- proof
  simp [Ge.of.Gt h]


-- created on 2025-06-07
