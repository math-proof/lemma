import Lemma.Nat.LtMulS.of.Lt.Gt_0
open Nat


@[main]
private lemma main
  [Mul α] [Zero α] [Preorder α] [MulPosStrictMono α]
  {x a b : α}
-- given
  (h₀ : a > b)
  (h₁ : x > 0) :
-- imply
  a * x > b * x :=
-- proof
  LtMulS.of.Lt.Gt_0 h₀ h₁


-- created on 2024-07-01
