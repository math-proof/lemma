import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : (if a = b then (1 : ℝ) else 0) ≠ 0) :
-- imply
  a = b := by
-- proof
  by_contra hc
  rw [ite_eq_right hc] at h
  exact h rfl


-- created on 2020-09-05
