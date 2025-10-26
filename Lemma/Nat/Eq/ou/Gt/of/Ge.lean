import Lemma.Nat.Eq.ou.Lt.of.Le
open Nat


@[main]
private lemma main
  [PartialOrder α]
  {a b : α}
-- given
  (h : a ≥ b) :
-- imply
  a = b ∨ a > b := by
-- proof
  rw [Eq.comm]
  apply Eq.ou.Lt.of.Le h


-- created on 2025-03-23
