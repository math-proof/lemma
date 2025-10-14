import Lemma.Algebra.Gt.of.LtNegS
import Lemma.Int.EqNegNeg
open Algebra Int


@[main]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {x y : α}
-- given
  (h : x < y) :
-- imply
  -x > -y := by
-- proof
  apply Gt.of.LtNegS
  repeat rw [EqNegNeg]
  assumption


-- created on 2025-03-29
