import Lemma.Int.EqNegNeg
import Lemma.Algebra.Lt.of.GtNegS
open Algebra Int


@[main]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {x y : α}
-- given
  (h : -x > y) :
-- imply
  x < -y := by
-- proof
  apply Lt.of.GtNegS
  rwa [EqNegNeg]


-- created on 2025-03-20
