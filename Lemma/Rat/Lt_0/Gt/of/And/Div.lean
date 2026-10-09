import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {x a b : ℝ}
-- given
  (h₀ : x < 0)
  (h₁ : a / x < b / x) :
-- imply
  x < 0 ∧ a > b := by
-- proof
  exact ⟨h₀, (div_lt_div_right_of_neg h₀).mp h₁⟩


-- created on 2023-10-03
