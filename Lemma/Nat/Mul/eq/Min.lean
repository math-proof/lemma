import sympy.Basic


@[main]
private lemma main
  {x y t : ℝ}
-- given
  (h : t > 0) :
-- imply
  t * min x y = min (t * x) (t * y) :=
-- proof
  mul_min_of_nonneg x y h.le


-- created on 2020-01-30
