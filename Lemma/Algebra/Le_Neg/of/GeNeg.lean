import Lemma.Algebra.EqNegNeg
import Lemma.Algebra.Le.of.GeNegS
open Algebra


@[main]
private lemma main
  [AddGroup α]
  [LE α]
  [AddLeftMono α]
  [AddRightMono α]
  {a : α}
-- given
  (h : a ≥ -b) :
-- imply
  -a ≤ b := by
-- proof
  apply Le.of.GeNegS
  rwa [EqNegNeg]


-- created on 2025-03-29
