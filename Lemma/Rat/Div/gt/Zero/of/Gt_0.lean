import Lemma.Nat.GtCoe_0.is.Gt_0
import Lemma.Rat.Div.gt.Zero.of.Div.gt.Zero
import Lemma.Rat.Div.gt.Zero.of.Gt_0.Gt_0
open Rat Nat


@[main]
private lemma main
  [NeZero (d : ℕ)]
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  d / x > 0 := by
-- proof
  have d_pos : (d : α) > 0 := by 
    apply GtCoe_0.of.Gt_0
    exact NeZero.pos d
  apply Div.gt.Zero.of.Gt_0.Gt_0 d_pos h


@[main]
private lemma left
  [NeZero (d : ℕ)]
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  x / d > 0 := by
-- proof
  apply Div.gt.Zero.of.Div.gt.Zero
  apply main h


-- created on 2025-07-19
-- updated on 2025-12-09
