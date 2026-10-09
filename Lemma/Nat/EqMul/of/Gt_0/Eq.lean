import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b x : ℝ}
-- given
  (_h₀ : x > 0)
  (h₁ : a = b) :
-- imply
  a * x = b * x := by
-- proof
  rw [h₁]


-- created on 2019-04-02
