import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : b ≥ x)
  (h₁ : x = a) :
-- imply
  a ≤ b := by
-- proof
  rw [← h₁]
  exact h₀


-- created on 2019-05-16
