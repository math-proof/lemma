import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a b : ℝ}
-- given
  (h₀ : x > 0)
  (h₁ : a / x = b / x) :
-- imply
  x > 0 ∧ a = b := by
-- proof
  exact ⟨h₀, (div_left_inj' h₀.ne').mp h₁⟩


-- created on 2023-03-26
