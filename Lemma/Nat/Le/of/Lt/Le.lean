import Lemma.Nat.Le.of.Le.Lt
open Nat


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : b ≤ c)
  (h₁ : a < b) :
-- imply
  a ≤ c := 
-- proof
  Le.of.Le.Lt h₁ h₀


-- created on 2025-06-20
