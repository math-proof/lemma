import sympy.sets.sets
import sympy.Basic


@[main]
private lemma both
  {x y : ℝ}
-- given
  (h₀ : x ≤ y)
  (h₁ : x ≥ -y) :
-- imply
  |x| ≤ |y| := by
-- proof
  exact (abs_le.mpr ⟨by linarith, h₀⟩).trans (le_abs_self y)


-- created on 2019-05-30
