import Lemma.Nat.Le.of.Le.Le
open Nat


@[main]
private lemma main
  [Preorder α]
  {x a b : α}
-- given
  (h₀ : x ≥ a)
  (h₁ : x ≤ b) :
-- imply
  a ≤ b := 
-- proof
  Le.of.Le.Le h₀ h₁


-- created on 2025-09-30
