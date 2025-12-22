import Lemma.Nat.GtCoe_0
import Lemma.Rat.Gt0Div.of.Gt_0.Lt_0
import Lemma.Rat.Gt0Div.of.Lt_0.Gt_0
open Rat Nat


@[main]
private lemma main
  [NeZero (d : ℕ)]
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x < 0) :
-- imply
  x / d < 0 := by
-- proof
  apply Gt0Div.of.Lt_0.Gt_0 h
  apply GtCoe_0


@[main]
private lemma left
  [NeZero (d : ℕ)]
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x < 0) :
-- imply
  d / x < 0 := by
-- proof
  apply Gt0Div.of.Gt_0.Lt_0 _ h
  apply GtCoe_0


-- created on 2025-07-20
-- updated on 2025-11-07
