import Lemma.Algebra.GeSquare_0
import Lemma.Algebra.Eq.of.Le.Ge
import Lemma.Algebra.Eq_0.of.EqSquare_0
open Algebra


@[main]
private lemma main
  [LinearOrderedRing α]
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
