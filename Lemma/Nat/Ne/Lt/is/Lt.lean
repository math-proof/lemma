import Lemma.Nat.Lt.Ne.is.Lt
open Nat


@[main]
private lemma main
  [Preorder α]
  {a b : α} :
-- imply
  a ≠ b ∧ a < b ↔ a < b := by
-- proof
  rw [And.comm]
  apply Lt.Ne.is.Lt


-- created on 2025-04-18
