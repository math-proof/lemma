import Lemma.Int.EqNegNeg
import Lemma.Int.Ge.of.LeNegS
open Int


@[main]
private lemma main
  [AddGroup α]
  [LE α]
  [AddLeftMono α]
  [AddRightMono α]
  {x y : α}
-- given
  (h : x ≤ y) :
-- imply
  -x ≥ - y := by
-- proof
  apply Ge.of.LeNegS
  repeat rw [EqNegNeg]
  assumption


-- created on 2025-03-29
