import sympy.Basic


@[main]
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
-- updated on 2025-03-20
