import sympy.Basic


@[main]
private lemma main
  {x a : ℝ} :
-- imply
  x = if a ≥ x then min x a else max x a := by
-- proof
  split_ifs with h
  ·
    exact (min_eq_left h).symm
  ·
    exact (max_eq_left (le_of_lt (not_le.mp h))).symm


-- created on 2026-09-27
