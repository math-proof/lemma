import Lemma.Int.LeCeil.is.Le
open Int


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
  apply not_le_of_gt h
  apply LeCeil.of.Le
  grind

-- created on 2018-10-30
-- updated on 2026-08-20
