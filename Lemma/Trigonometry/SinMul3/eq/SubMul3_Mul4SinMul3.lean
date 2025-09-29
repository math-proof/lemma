import sympy.functions.elementary.trigonometric
import sympy.Basic


/--
This lemma establishes the triple-angle identity for the sine function, demonstrating that `sin(3 * x)` can be expressed in terms of `sin(x)` as `3 * sin(x) - 4 * (sin(x)) ^ 3`.
It provides a fundamental trigonometric relationship used to simplify expressions involving multiple angles.
-/
@[main]
private lemma main
  {x : ℝ} :
-- imply
  sin (3 * x) = 3 * sin x - 4 * (sin x) ^ 3 := by
-- proof
  apply Real.sin_three_mul x


-- created on 2025-03-24
-- updated on 2025-04-04
