import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : a > 0)
  (h₁ : b ^ 2 - 4 * a * c > 0) :
-- imply
  ∃ x, a * x ^ 2 + b * x + c < 0 := by
-- proof
  have ha : a ≠ 0 := h₀.ne'
  have e : a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c = -(b ^ 2 - 4 * a * c) / (4 * a) := by
    field_simp
    ring
  refine ⟨-b / (2 * a), ?_⟩
  rw [e]
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)


-- created on 2026-09-27
