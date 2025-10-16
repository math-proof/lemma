import Lemma.Nat.NotLe.is.Gt
import Lemma.Algebra.GtMulS.of.Gt_0.Gt
import Lemma.Algebra.NotLe.of.Gt
open Algebra Nat


@[main]
private lemma main
  [Mul α] [Zero α] [LinearOrder α] [PosMulStrictMono α]
  {x a b : α}
-- given
  (h₀ : x > 0)
  (h₁ : x * a ≤ x * b) :
-- imply
  a ≤ b := by
-- proof
  by_contra h
  have := Gt.of.NotLe h
  have := GtMulS.of.Gt_0.Gt h₀ this
  have := NotLe.of.Gt this
  contradiction


-- created on 2025-04-06
