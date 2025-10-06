import Lemma.Algebra.EqNegNeg
import Lemma.Algebra.Gt.of.LtNegS
open Algebra


@[main]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {x y : α}
-- given
  (h : -x < y) :
-- imply
  x > -y := by
-- proof
  apply Gt.of.LtNegS
  rwa [EqNegNeg]


-- created on 2025-03-20
