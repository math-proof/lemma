import Lemma.Nat.Ge.of.Ge.Ge
open Nat


@[path]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : b > c) :
-- imply
  a ≥ c := by
-- proof
  apply Ge.of.Ge.Ge h₀ (le_of_lt h₁)


-- created on 2025-06-20
-- updated on 2026-11-23
