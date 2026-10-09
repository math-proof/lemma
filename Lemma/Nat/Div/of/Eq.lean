import sympy.Basic


@[path]
private lemma left
  [Div α]
  {x y : α}
-- given
  (h : x = y)
  (d : α) :
-- imply
  d / x = d / y := by
-- proof
  rw [h]


@[path]
private lemma main
  [Div α]
  {x y : α}
-- given
  (h : x = y)
  (d : α) :
-- imply
  x / d = y / d := by
-- proof
  rw [h]


-- created on 2018-08-21
