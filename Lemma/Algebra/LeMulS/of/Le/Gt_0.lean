import Lemma.Nat.Ge.of.Gt
import Lemma.Algebra.LeMulS.of.Le.Ge_0
open Algebra Nat


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosMono α]
  {x a b : α}
-- given
  (h₀ : a ≤ b)
  (h₁ : x > 0) :
-- imply
  a * x ≤ b * x :=
-- proof
  LeMulS.of.Le.Ge_0 h₀ (Ge.of.Gt h₁)


-- created on 2024-07-01
