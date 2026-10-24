import Mathlib
import sympy.Basic


namespace MetaMathlibExt

/--
[pellType_solution_mul_unit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/PellTypeSolutionMulUnit.lean)
-/
@[path]
lemma pellType_solution_mul_unit
  {a b c T U x y : ℤ}
-- given
  (hsol : a * T ^ 2 - b * U ^ 2 = c)
  (hunit : x ^ 2 - a * b * y ^ 2 = 1) :
-- imply
  a * (T * x + b * U * y) ^ 2 - b * (a * T * y + U * x) ^ 2 = c := by
-- proof
  linear_combination (x ^ 2 - a * b * y ^ 2) * hsol + c * hunit

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
