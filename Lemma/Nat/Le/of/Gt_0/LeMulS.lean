import Lemma.Nat.NotLe.is.Gt
import Lemma.Nat.LtMulS.of.Gt_0.Lt
import Lemma.Nat.NotLe.of.Gt
open Nat


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
