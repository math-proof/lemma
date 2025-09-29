import sympy.Basic


@[main]
private lemma main
  [LT α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  y < x := by
-- proof
  simp [h]


-- created on 2024-07-01
