import Lemma.Algebra.EqNegNeg
import Lemma.Algebra.Ge.of.LeNegS
open Algebra


@[main]
private lemma main
  [AddGroup α]
  [LE α]
  [AddLeftMono α]
  [AddRightMono α]
  {a : α}
-- given
  (h : a ≤ -b) :
-- imply
  -a ≥ b := by
-- proof
  apply Ge.of.LeNegS
  rwa [EqNegNeg]


-- created on 2025-03-29
