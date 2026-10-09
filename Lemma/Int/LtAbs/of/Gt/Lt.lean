import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x > -y)
  (h₁ : x < y) :
-- imply
  |x| < y := by
-- proof
  exact abs_lt.mpr ⟨by linarith, h₁⟩


-- created on 2023-04-15
