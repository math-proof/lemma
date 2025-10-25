import Lemma.Nat.Ge.of.Gt
import Lemma.Int.GeMulS.of.Ge.Ge_0
open Nat Int


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h₀ : a ≥ b)
  (h₁ : x > 0) :
-- imply
  a * x ≥ b * x := by
-- proof
  have h := Ge.of.Gt h₁
  apply GeMulS.of.Ge.Ge_0 h₀ h


-- created on 2024-07-01
