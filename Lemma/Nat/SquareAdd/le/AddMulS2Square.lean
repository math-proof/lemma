import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import sympy.Basic


@[main]
private lemma main
  [CommSemiring α] [LinearOrder α] [ExistsAddOfLE α] [MulPosStrictMono α] [AddLeftReflectLE α] [AddLeftMono α]
-- given
  (x y : α) :
-- imply
  (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
-- proof
  rw [add_sq]
  have := two_mul_le_add_sq x y
  calc
    _  ≤ x ^ 2 + (x ^ 2 + y ^ 2) + y ^ 2 := by gcongr
    _ = _ := by ring


-- created on 2026-09-18
