import Lemma.Int.EqAbs_0.is.Eq_0
open Int


@[main]
private lemma main
  [AddGroup α] [LinearOrder α] [AddLeftMono α] [AddRightMono α]
  {a : α}
-- given
  (h : a ≠ 0) :
-- imply
  |a| ≠ 0 := by
-- proof
  by_contra h
  have := Eq_0.of.EqAbs_0 h
  contradiction


-- created on 2025-01-14
-- updated on 2025-10-16
