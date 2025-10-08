import Lemma.Nat.Ge.of.Gt
import Lemma.Algebra.GeMulS.of.Ge_0.Ge
open Algebra Nat


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulMono α]
  {x a b : α}
-- given
  (h₀ : x ≥ 0)
  (h₁ : a > b) :
-- imply
  x * a ≥ x * b := by
-- proof
  have h := Ge.of.Gt h₁
  apply GeMulS.of.Ge_0.Ge h₀ h


-- created on 2024-07-01
