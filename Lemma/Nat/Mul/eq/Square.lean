import Mathlib.Basic.Real.Basic
import sympy.Basic


@[path]
private lemma main
  {a : ℝ} :
-- imply
  a * a = a ^ 2 :=
-- proof
  (pow_two a).symm


-- created on 2020-01-02
