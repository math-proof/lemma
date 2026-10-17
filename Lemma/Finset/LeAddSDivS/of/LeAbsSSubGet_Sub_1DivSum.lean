import Mathlib.Algebra.Order.Ring.Abs
import sympy.Basic


@[path]
private lemma main
  {n m : ℕ}
  (x : Fin n → ℝ)
  (y : Fin m → ℝ)
  (a : ℝ)
-- given
  (h₀ : |a - (∑ i, x i) / n| ≤ |a - (∑ j, y j) / m|) :
-- imply
  (a - (∑ i, x i) / n) ^ 2 ≤ (a - (∑ j, y j) / m) ^ 2 := by
-- proof
  simpa [sq_abs] using (sq_le_sq.mpr h₀)


-- created on 2019-11-09
-- updated on 2026-10-17
