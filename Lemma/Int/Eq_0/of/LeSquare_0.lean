import Lemma.Int.GeSquare_0
import Lemma.Nat.Eq.of.Le.Ge
import Lemma.Int.Eq_0.is.EqSquare_0
open Nat Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x² ≤ 0) :
-- imply
  x = 0 := by
-- proof
  have := GeSquare_0 (a := x)
  have := Eq.of.Le.Ge h this
  apply Eq_0.of.EqSquare_0 this


-- created on 2025-04-06
