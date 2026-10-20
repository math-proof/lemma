import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.LegendreThreeSquare
open Nat


/--
[exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/LegendreThreeSquare.lean)
-/
@[path]
private lemma exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven_eq
  {n : Nat}
-- given
  (h : ¬ ∃ a b : Nat, n = 4 ^ a * (8 * b + 7)) :
-- imply
  ∃ x y z : Nat, x ^ 2 + y ^ 2 + z ^ 2 = n := by
-- proof
  apply Nat.exists_three_squares_of_not_four_pow_mul_eight_mul_add_seven n h


-- created on 2026-10-20
