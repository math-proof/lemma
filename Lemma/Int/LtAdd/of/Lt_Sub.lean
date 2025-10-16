import sympy.Basic


@[main]
private lemma main
  [AddGroup α]
  [LT α]
  [AddRightStrictMono α]
  {a b c : α}
-- given
  (h : a < c - b) :
-- imply
  a + b < c :=
-- proof
  add_lt_of_lt_sub_right h


@[main]
private lemma left
  [AddCommGroup α]
  [LT α]
  [AddLeftStrictMono α]
  {a b c : α}
-- given
  (h : b < c - a) :
-- imply
  a + b < c :=
-- proof
  add_lt_of_lt_sub_left h


-- created on 2025-10-16
