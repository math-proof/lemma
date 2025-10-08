import Lemma.Nat.Le.of.Lt
import Lemma.Algebra.Mul.lt.Zero.of.Lt_0.Gt_0
open Algebra Nat


@[main]
private lemma main
  [MulZeroClass α]
  [Preorder α]
  [MulPosStrictMono α]
  {x y : α}
-- given
  (h₀ : x < 0)
  (h₁ : y > 0) :
-- imply
  x * y ≤ 0 := by
-- proof
  apply Le.of.Lt
  apply Mul.lt.Zero.of.Lt_0.Gt_0 h₀ h₁


-- created on 2025-03-24
