import Lemma.Int.EqAbs_0.is.Eq_0
open Int


@[main]
private lemma main
  [AddGroup α] [LinearOrder α] [AddLeftMono α] [AddRightMono α]
  {x : α}
-- given
  (h : |x| ≠ 0) :
-- imply
  x ≠ 0 := by
-- proof
  by_contra h
  have := EqAbs_0.of.Eq_0 h
  contradiction


-- created on 2025-04-18
-- updated on 2025-08-02
