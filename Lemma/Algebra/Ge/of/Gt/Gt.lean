import Lemma.Nat.Ge.of.Gt
import Lemma.Algebra.Gt.of.Gt.Gt
open Algebra Nat


@[main]
private lemma main
  [Preorder α]
  {a b c : α}
-- given
  (h₀ : a > b)
  (h₁ : b > c) :
-- imply
  a ≥ c := by
-- proof
  apply Ge.of.Gt
  apply Gt.of.Gt.Gt h₀ h₁


-- created on 2025-05-18
