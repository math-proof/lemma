import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Diophantine.PowerSquare
open Nat


/--
[eq_zero_of_three_pow_succ_add_one_eq_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Diophantine/PowerSquare.lean)
-/
@[path]
private lemma eq_zero_of_three_pow_succ_add_one_eq_sq_eq
  {y z : ℕ}
-- given
  (h : 3 ^ (y + 1) + 1 = z ^ 2) :
-- imply
  y = 0 := by
-- proof
  apply Nat.eq_zero_of_three_pow_succ_add_one_eq_sq h


-- created on 2026-10-20
