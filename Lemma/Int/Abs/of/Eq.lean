import sympy.Basic


@[main]
private lemma main
  [AddCommGroup α] [LinearOrder α]
  {x y : α}
-- given
  (h : x = y) :
-- imply
  |x| = |y| := by
-- proof
  rw [h]


-- created on 2018-06-05
