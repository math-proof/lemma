import sympy.Basic


@[path]
private lemma main
  {a b c : ℕ}
-- given
  (h : a < c - b) :
-- imply
  a + b < c :=
-- proof
  Nat.add_lt_of_lt_sub h


@[path]
private lemma left
  {a b c : ℕ}
-- given
  (h : b < c - a) :
-- imply
  a + b < c :=
-- proof
  Nat.add_lt_of_lt_sub' h


-- created on 2025-04-06
-- updated on 2025-10-16
