import Lemma.Rat.Div.gt.Zero.is.AndGtS_0.ou.AndLtS_0
import Lemma.Rat.Div.gt.Zero.of.Gt_0.Gt_0
import Lemma.Rat.Div.gt.Zero.of.Lt_0.Lt_0
open Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {x y : α}
-- given
  (h : y / x > 0) :
-- imply
  x / y > 0 := by
-- proof
  obtain ⟨hx, hy⟩ | ⟨hy, hx⟩ := AndGtS_0.ou.AndLtS_0.of.Div.gt.Zero h
  ·
    apply Div.gt.Zero.of.Gt_0.Gt_0
    repeat assumption
  ·
    apply Div.gt.Zero.of.Lt_0.Lt_0
    repeat assumption


-- created on 2025-12-08
