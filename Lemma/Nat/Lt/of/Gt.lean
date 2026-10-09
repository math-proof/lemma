import sympy.Basic


@[path]
private lemma main
  [LT α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  y < x := by
-- proof
  simp [h]


@[path]
private lemma reverse.given
  [LT α]
  {x a : α}
-- given
  (h : a > x) :
-- imply
  x < a := by
-- proof
  exact h


-- created on 2019-12-17
-- updated on 2026-09-27
