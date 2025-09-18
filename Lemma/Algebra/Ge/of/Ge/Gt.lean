import Lemma.Algebra.Ge.of.Ge.Ge
import Lemma.Algebra.Ge.of.Gt
open Algebra


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a > b)
  (h₁ : b ≥ c) :
-- imply
  a ≥ c := by
-- proof
  apply Ge.of.Ge.Ge _ h₁
  apply Ge.of.Gt h₀


-- created on 2025-06-20
