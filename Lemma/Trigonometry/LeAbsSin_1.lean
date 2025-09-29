import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
  {x : ℝ} :
-- imply
  |sin x| ≤ 1 :=
-- proof
  Real.abs_sin_le_one x


-- created on 2025-03-25
