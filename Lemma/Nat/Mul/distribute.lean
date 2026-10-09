import sympy.Basic


@[path]
private lemma main
  {a b c d r : ℝ} :
-- imply
  (-r) * (a - b - c) / d =
    (a * (-r) + (-b) * (-r) + (-c) * (-r)) / d := by
-- proof
  congr 1
  ring


-- created on 2018-08-19
