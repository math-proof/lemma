import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {c : ℝ}
  {x y : ℂ} :
-- imply
  re (c * x + c * y) = c * re (x + y) := by
-- proof
  rw [← mul_add, Complex.re_ofReal_mul]


-- created on 2023-06-23
