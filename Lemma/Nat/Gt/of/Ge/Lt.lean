import Lemma.Nat.Gt.of.Ge.Gt
open Nat


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : b ≥ c)
  (h₁ : a < c) :
-- imply
  b > a :=
-- proof
  Gt.of.Ge.Gt h₀ h₁


-- created on 2025-10-01
