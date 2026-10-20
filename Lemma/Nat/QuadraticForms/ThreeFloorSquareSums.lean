import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.ThreeFloorSquareSums
open MetaMathlibExt


/--
[every_nat_eq_sum_three_sq_div_eight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeFloorSquareSums.lean)
-/
@[path]
private lemma every_nat_eq_sum_three_sq_div_eight_eq
  {m : ℕ} :
-- imply
  ∃ a b c : ℕ, m = a ^ 2 / 8 + b ^ 2 / 8 + c ^ 2 / 8 := by
-- proof
  apply MetaMathlibExt.every_nat_eq_sum_three_sq_div_eight m


-- created on 2026-10-20
