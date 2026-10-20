import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.DifferenceOfTwoSquares
open MetaMathlibExt


/--
[nat_eq_sq_sub_sq_iff_not_eq_four_mul_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/DifferenceOfTwoSquares.lean)
-/
@[path]
private lemma nat_eq_sq_sub_sq_iff_not_eq_four_mul_add_two_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∃ a b : ℕ, n = a ^ 2 - b ^ 2) ↔ ¬ ∃ k : ℕ, n = 4 * k + 2 := by
-- proof
  apply MetaMathlibExt.nat_eq_sq_sub_sq_iff_not_eq_four_mul_add_two n hn


-- created on 2026-10-20
