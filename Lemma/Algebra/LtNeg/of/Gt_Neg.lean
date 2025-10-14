import Lemma.Algebra.Lt.of.GtNegS
import Lemma.Int.EqNegNeg
open Algebra Int


@[main]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {a : α}
-- given
  (h : a > -b) :
-- imply
  -a < b := by
-- proof
  apply Lt.of.GtNegS
  rwa [EqNegNeg]


-- created on 2025-03-29
