import Lemma.Int.Abs.eq.IteGt_0
open Int


@[main]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  {x : α}
-- given
  (h : x > 0) :
-- imply
  |x| = x := by
-- proof
  rw [Abs.eq.IteGt_0]
  rw [if_pos h]


-- created on 2025-10-01
