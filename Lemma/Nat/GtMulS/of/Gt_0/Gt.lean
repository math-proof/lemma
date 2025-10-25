import Lemma.Algebra.LtMulS.of.Gt_0.Lt
open Algebra


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [PosMulStrictMono α]
  {x a b : α}
-- given
  (h₀ : x > 0)
  (h₁ : a > b) :
-- imply
  x * a > x * b :=
-- proof
  LtMulS.of.Gt_0.Lt h₀ h₁


-- created on 2024-07-01
