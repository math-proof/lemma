import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {x y : Fin n → ℝ}
-- given
  (h : (if x = y then (1 : ℝ) else 0) = 1) :
-- imply
  x = y := by
-- proof
  by_contra hc
  rw [if_neg hc] at h
  exact zero_ne_one h


-- created on 2019-04-20
