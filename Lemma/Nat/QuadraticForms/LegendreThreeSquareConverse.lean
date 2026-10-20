import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.LegendreThreeSquareConverse
open Nat


/--
[not_exists_four_pow_mul_eight_mul_add_seven_of_exists_three_squares](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquareConverse.lean)
-/
@[path]
private lemma not_exists_four_pow_mul_eight_mul_add_seven_of_exists_three_squares_eq
  {n : Nat}
-- given
  (h : ∃ x y z : Nat, x ^ 2 + y ^ 2 + z ^ 2 = n) :
-- imply
  ¬ ∃ a b : Nat, n = 4 ^ a * (8 * b + 7) := by
-- proof
  apply Nat.not_exists_four_pow_mul_eight_mul_add_seven_of_exists_three_squares n h


-- created on 2026-10-20
