import Lemma.Algebra.Ceil.le.Zero.of.Le_0
open Algebra


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  [FloorRing α]
  {x : α}
-- given
  (h : ⌈x⌉ > 0) :
-- imply
  x > 0 := by
-- proof
  by_contra hx
  have := Ceil.le.Zero.of.Le_0 (le_of_not_gt hx)
  exact not_le_of_gt h this


-- created on 2018-10-30
-- updated on 2026-08-20
