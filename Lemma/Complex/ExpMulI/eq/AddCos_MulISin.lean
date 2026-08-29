import sympy.functions.elementary.complexes
import sympy.functions.elementary.trigonometric
import sympy.Basic


@[main]
private lemma main
-- given
  (x : ℂ) :
-- imply
  (I * x).exp = x.cos + I * x.sin := by
-- proof
  rw [mul_comm, Complex.exp_mul_I, mul_comm]


-- created on 2025-10-07
-- updated on 2026-08-29
