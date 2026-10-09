import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x ≤ y)
  (h₁ : -x ≤ y) :
-- imply
  |x| ≤ y := by
-- proof
  exact abs_le.mpr ⟨by linarith, h₀⟩


-- created on 2022-01-07
