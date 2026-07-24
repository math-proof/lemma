import sympy.Basic


@[main]
private lemma left
  [Mul α]
  {x y : α}
-- given
  (h : x = y)
  (d : α) :
-- imply
  d * x = d * y := by
-- proof
  rw [h]


@[main]
private lemma main
  [Mul α]
  {x y : α}
-- given
  (h : x = y)
  (d : α) :
-- imply
  x * d = y * d := by
-- proof
  rw [h]


-- created on 2024-11-28
