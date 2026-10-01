import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : a ≤ x)
  (h₁ : x = b) :
-- imply
  a ≤ b := by
-- proof
  rw [← h₁]
  exact h₀


-- created on 2019-10-24
