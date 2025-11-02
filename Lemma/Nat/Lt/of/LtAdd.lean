import sympy.Basic


@[main]
private lemma left
  {a b c : ℕ}
-- given
  (h : a + b < c) :
-- imply
  a < c := by
-- proof
  omega


@[main]
private lemma main
  {a b c : ℕ}
-- given
  (h : a + b < c) :
-- imply
  b < c := by
-- proof
  omega


-- created on 2025-11-02
