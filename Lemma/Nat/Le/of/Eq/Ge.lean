import sympy.sets.sets
import sympy.Basic


@[main]
private lemma subst
  {y b x t k : ℝ}
-- given
  (hk : k < 0)
  (h₀ : y = x * k + b)
  (h₁ : x ≥ t) :
-- imply
  y ≤ t * k + b := by
-- proof
  nlinarith


-- created on 2021-09-20
