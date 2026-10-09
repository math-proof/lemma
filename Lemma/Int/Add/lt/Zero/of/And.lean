import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given
  {a b c : ℝ}
-- given
  (h₀ : a + b ≤ 0)
  (h₁ : c < 0) :
-- imply
  a + b + c < 0 := by
-- proof
  linarith


-- created on 2018-11-30
