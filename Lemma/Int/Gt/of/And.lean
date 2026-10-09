import sympy.sets.sets
import sympy.Basic


@[path]
private lemma given.scale.negative
  {x y z : ℝ}
-- given
  (h₀ : x * z < y * z)
  (h₁ : z < 0) :
-- imply
  x > y := by
-- proof
  nlinarith


-- created on 2026-09-27
