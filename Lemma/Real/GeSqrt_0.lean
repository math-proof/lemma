import sympy.core.power
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  √x ≥ 0 := by
-- proof
  -- By definition, the square root of a real number x is only defined for x ≥ 0.
  -- The principal square root of x, denoted √x, is the unique non-negative real number y such that y^2 = x.
  -- Therefore, √x ≥ 0 for all x in the domain x ≥ 0.
  exact Real.sqrt_nonneg x


-- created on 2025-04-06
-- updated on 2025-07-20
