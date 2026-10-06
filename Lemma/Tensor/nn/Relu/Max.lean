import sympy.Basic


@[main]
private lemma main
  {x y : ℝ} :
-- imply
  max (x - y) 0 + y = max x y := by
-- proof
  by_cases h : x ≤ y
  · rw [max_eq_right (by linarith), max_eq_right h]
    linarith
  · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith


-- created on 2021-01-05
