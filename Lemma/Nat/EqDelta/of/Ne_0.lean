import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b : ℝ}
-- given
  (h : (if a = b then (1 : ℝ) else 0) ≠ 0) :
-- imply
  a = b := by
-- proof
  by_contra hc
  rw [if_neg hc] at h
  exact h rfl


-- created on 2026-09-27
