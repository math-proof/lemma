import Lemma.Nat.Eq_0.is.EqSquare_0
import Lemma.Nat.Gt.is.Ge.Ne
open Nat


@[main]
private lemma main
  [Semiring α] [LinearOrder α] [ExistsAddOfLE α] [PosMulMono α] [AddLeftMono α]
  [NoZeroDivisors α] [NeZero (1 : α)]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  a² > 0 :=
-- proof
  Gt.of.Ge.Ne (sq_nonneg a) (NeSquare_0.of.Ne_0 h)


-- created on 2024-11-29
-- updated on 2025-03-30
