import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b : ℝ}
-- given
  (h : a > 0) :
-- imply
  ∃ x, a * x + b > 0 := by
-- proof
  have ha : a ≠ 0 := h.ne'
  have e : a * ((1 - b) / a) = 1 - b := by field_simp
  refine ⟨(1 - b) / a, ?_⟩
  rw [e]
  linarith


-- created on 2022-04-03
