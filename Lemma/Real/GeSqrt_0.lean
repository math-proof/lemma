import sympy.core.power
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℝ) :
-- imply
  √x ≥ 0 :=
-- proof
  Real.sqrt_nonneg x


-- created on 2025-04-06
-- updated on 2025-07-20
