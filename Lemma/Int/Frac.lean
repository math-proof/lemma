import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma half
  {n : ℤ} :
-- imply
  Int.fract (-(n : ℝ) / 2) = Int.fract ((n : ℝ) / 2) := by
-- proof
  rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [show -((k + k : ℤ) : ℝ) / 2 = ((-k : ℤ) : ℝ) by push_cast; ring, show ((k + k : ℤ) : ℝ) / 2 = ((k : ℤ) : ℝ) by push_cast; ring,
      Int.fract_intCast, Int.fract_intCast]
  · rw [show -((2 * k + 1 : ℤ) : ℝ) / 2 = ((-k - 1 : ℤ) : ℝ) + 1 / 2 by push_cast; ring,
      show ((2 * k + 1 : ℤ) : ℝ) / 2 = ((k : ℤ) : ℝ) + 1 / 2 by push_cast; ring, Int.fract_intCast_add, Int.fract_intCast_add]


-- created on 2019-05-10
