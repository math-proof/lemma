import Lemma.Nat.Ne.of.Lt
open Nat


@[main]
private lemma main
  [Preorder α]
  {a b : α} :
-- imply
  a < b ∧ a ≠ b ↔ a < b := by
-- proof
  constructor <;> intro h
  -- Forward direction (→): If `a < b ∧ a ≠ b`, then `a < b`.
  -- This is straightforward by taking the first component of the conjunction.
  exact h.1
  -- Reverse direction (←): If `a < b`, then `a < b ∧ a ≠ b`.
  -- Use the fact that in a linear order, `a < b` implies `a ≠ b`.
  exact ⟨h, Ne.of.Lt h⟩


-- created on 2025-04-18
