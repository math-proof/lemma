import Lemma.Int.GtAbs_0.of.Ne_0
import Lemma.Nat.Ne.of.Lt
open Int Nat


@[main]
private lemma main
  [AddGroup α] [LinearOrder α] [AddLeftMono α] [AddRightMono α]
  {a : α}
-- given
  (h : a < 0) :
-- imply
  |a| > 0 := by
-- proof
  apply GtAbs_0.of.Ne_0
  apply Ne.of.Lt h


-- created on 2025-12-22
