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
  [AddLeftStrictMono  α]
  {a b c : α}
-- given
  (h : b < c - a) :
-- imply
  a + b < c :=
-- proof
  add_lt_of_lt_sub_left h


@[main]
private lemma nat
  {a b c : ℕ}
-- given
  (h : a < c - b) :
-- imply
  a + b < c :=
-- proof
  Nat.add_lt_of_lt_sub h


@[main]
private lemma left.nat
  {a b c : ℕ}
-- given
  (h : b < c - a) :
-- imply
  a + b < c :=
-- proof
  Nat.add_lt_of_lt_sub' h


-- created on 2025-04-06
-- updated on 2025-06-28
