import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (h₀ : b ≥ x)
  (h₁ : x ≥ a) :
-- imply
  a ≤ b := by
-- proof
  exact le_trans h₁ h₀


-- created on 2019-05-20
