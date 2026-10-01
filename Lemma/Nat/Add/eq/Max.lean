import sympy.Basic


@[main]
private lemma main
  {x y z : ℝ} :
-- imply
  max x y - z = max (x - z) (y - z) :=
-- proof
  (max_sub_sub_right x y z).symm


-- created on 2018-08-06
