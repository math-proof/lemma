import Lemma.Nat.GtSquare_0.of.Ne_0
import Lemma.Nat.Ne.of.Gt
open Nat


@[main]
private lemma main
  [Semiring α] [LinearOrder α] [ExistsAddOfLE α] [PosMulMono α] [AddLeftMono α]
  [NoZeroDivisors α] [NeZero (1 : α)]
  {a : α}
-- given
  (h : a > 0) :
-- imply
  a² > 0 := by
-- proof
  have := Ne.of.Gt h
  apply GtSquare_0.of.Ne_0 this


-- created on 2025-04-06
