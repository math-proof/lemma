import sympy.Basic


@[main]
private lemma main
  {x y z : ℝ} :
-- imply
  min x y - z = min (x - z) (y - z) :=
-- proof
  (min_sub_sub_right x y z).symm


-- created on 2026-09-27
