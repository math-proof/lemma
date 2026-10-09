import Mathlib.Algebra.Order.Floor.Ring
import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {x : ℤ} :
-- imply
  ⌊((x : ℝ) - 1) / 2⌋ = x - ⌊(x : ℝ) / 2⌋ - 1 := by
-- proof
  have h0 : ⌊(1 / 2 : ℝ)⌋ = 0 := by rw [Int.floor_eq_zero_iff]; norm_num
  rcases Int.even_or_odd' x with ⟨k, rfl | rfl⟩
  · rw [show (((2 * k : ℤ) : ℝ) - 1) / 2 = ((k - 1 : ℤ) : ℝ) + 1 / 2 by push_cast; ring,
      show ((2 * k : ℤ) : ℝ) / 2 = ((k : ℤ) : ℝ) by push_cast; ring, Int.floor_intCast_add, Int.floor_intCast, h0]
    ring
  · rw [show (((2 * k + 1 : ℤ) : ℝ) - 1) / 2 = ((k : ℤ) : ℝ) by push_cast; ring,
      show ((2 * k + 1 : ℤ) : ℝ) / 2 = ((k : ℤ) : ℝ) + 1 / 2 by push_cast; ring, Int.floor_intCast_add, Int.floor_intCast, h0]
    ring


-- created on 2019-05-11
