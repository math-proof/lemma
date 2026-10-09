import sympy.Basic


@[path]
private lemma main
  {x y c : ℝ}
-- given
  (hxy : x > y)
  (hc : c < 0) :
-- imply
  x * c < y * c :=
-- proof
  mul_lt_mul_of_neg_right hxy hc


-- created on 2019-07-15
