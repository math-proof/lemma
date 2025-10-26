import Lemma.Int.EqNegNeg
import Lemma.Int.Lt.of.GtNegS
open Int


@[main]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  -x < -y := by
-- proof
  apply Lt.of.GtNegS
  repeat rw [EqNegNeg]
  assumption


-- created on 2025-03-29
