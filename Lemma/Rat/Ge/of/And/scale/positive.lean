import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {x y z : ℝ}
  -- given
  (h : y ≤ x)
  (hpos : 0 < z)
  -- imply
  : y * z ≤ x * z ∧ 0 < z := by
  -- proof
  exact ⟨mul_le_mul_of_nonneg_right h (le_of_lt hpos), hpos⟩

-- created on 2019-05-22
