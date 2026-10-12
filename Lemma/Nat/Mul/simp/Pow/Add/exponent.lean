import Mathlib.Basic.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {x : ℝ}
  {m n : ℕ} :
-- imply
  x ^ m * x ^ n = x ^ (m + n) :=
-- proof
  (pow_add x m n).symm


-- created on 2022-07-07
