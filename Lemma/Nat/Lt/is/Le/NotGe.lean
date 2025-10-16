import Lemma.Nat.Lt.is.Le.NotLe
open Nat


@[main, comm, mp, mpr]
private lemma main
  [Preorder α]
  {a b : α} :
-- imply
  a < b ↔ a ≤ b ∧ ¬(a ≥ b) := by
-- proof
  apply Lt.is.Le.NotLe


-- created on 2025-08-02
