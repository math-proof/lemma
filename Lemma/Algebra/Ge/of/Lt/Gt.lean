import Lemma.Algebra.Ge.of.Gt.Gt
open Algebra


@[main]
private lemma main
  [Preorder α]
  {x a b : α}
-- given
  (h₀ : x < b)
  (h₁ : x > a) :
-- imply
  b ≥ a :=
-- proof
  Ge.of.Gt.Gt h₀ h₁


-- created on 2025-10-01
