import sympy.Basic


@[main]
private lemma main
  {x y z : ℝ} :
-- imply
  max (x - y) 0 + min y z ≥ min x z := by
-- proof
  by_cases h : x ≤ y
  · rw [max_eq_right (by linarith)]
    have hm : min x z ≤ min y z := by
      apply min_le_min
      · linarith
      · rfl
    linarith
  · rw [max_eq_left (by linarith)]
    by_cases hz : z ≤ y
    · rw [min_eq_right hz, min_eq_right (by linarith)]
      linarith
    · rw [min_eq_left (by linarith)]
      linarith [min_le_left x z]


-- created on 2020-12-27
-- updated on 2022-01-08
