import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [AddGroup α]
  [LT α]
  [AddLeftStrictMono α]
  [AddRightStrictMono α]
  {x y : α}
-- given
  (h : -x < -y) :
-- imply
  x > y := by
-- proof
  exact lt_of_neg_lt_neg h


-- created on 2024-07-01
-- updated on 2026-10-26
