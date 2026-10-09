import Mathlib.Analysis.Complex.Basic
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {f : ℤ → ℂ}
  {x y : ℤ} :
-- imply
  (f x - f y) * (if x = y then 1 else 0) = 0 := by
-- proof
  split_ifs with h
  · rw [h, sub_self, zero_mul]
  · rw [mul_zero]


-- created on 2022-10-11
