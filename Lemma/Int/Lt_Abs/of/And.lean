import sympy.sets.sets
import sympy.Basic


@[main]
private lemma given
  {x a : ℤ}
-- given
  (h₀ : x < a)
  (h₁ : x > -a) :
-- imply
  |x| < a := by
-- proof
  exact abs_lt.mpr ⟨by linarith, h₀⟩


-- created on 2019-12-18
