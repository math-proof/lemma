import sympy.Basic


@[main]
private lemma main
  {x : ℝ}
-- given
  (h : x > 1) :
-- imply
  x.log > 0 :=
-- proof
  Real.log_pos h


-- created on 2025-12-28
