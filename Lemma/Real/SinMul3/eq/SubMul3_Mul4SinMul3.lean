import sympy.core.power
import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  sin (3 * x) = 3 * sin x - 4 * (sin x)³ :=
-- proof
  Real.sin_three_mul x


-- created on 2025-03-24
-- updated on 2025-04-04
