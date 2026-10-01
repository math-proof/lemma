import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {x y : ℝ}
-- given
  (h₀ : x < y)
  (h₁ : x > -y) :
-- imply
  |x| < y := by
-- proof
  exact abs_lt.mpr ⟨h₁, h₀⟩


@[main]
private lemma both
  {x y : ℝ}
-- given
  (h₀ : x < y)
  (h₁ : x > -y) :
-- imply
  |x| < |y| := by
-- proof
  exact (abs_lt.mpr ⟨h₁, h₀⟩).trans_le (le_abs_self y)


-- created on 2018-07-29
