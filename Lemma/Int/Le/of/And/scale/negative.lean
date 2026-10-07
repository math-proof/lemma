import sympy.Basic


@[main]
private lemma main
  {x y c : ℝ}
-- given
  (hxy : x ≤ y)
  (hc : c < 0) :
-- imply
  x * c ≥ y * c :=
-- proof
  mul_le_mul_of_nonpos_right hxy (le_of_lt hc)


-- created on 2019-07-15
