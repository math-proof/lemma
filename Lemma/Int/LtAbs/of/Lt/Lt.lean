import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x < y)
  (h₁ : -x < y) :
-- imply
  |x| < y := by
-- proof
  exact abs_lt.mpr ⟨by linarith, h₀⟩


-- created on 2026-09-27
