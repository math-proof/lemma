import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.QuadraticForms.FibonacciNormEquation
open FibonacciNormEquation


/--
[fibonacci_norm_eq_one_or_neg_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/FibonacciNormEquation.lean)
-/
@[path]
private lemma fibonacci_norm_eq_one_or_neg_one_iff_eq
  {x y : ℤ} :
-- imply
  (x ^ 2 - x * y - y ^ 2 = 1 ∨ x ^ 2 - x * y - y ^ 2 = -1) ↔
    ∃ n s : ℤ, (s = 1 ∨ s = -1) ∧ x = s * Int.fib n ∧ y = s * Int.fib (n - 1) := by
-- proof
  apply FibonacciNormEquation.fibonacci_norm_eq_one_or_neg_one_iff x y


-- created on 2026-10-20
