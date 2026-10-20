import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GibonacciNumber
open MetaMathlibExt


/--
[gibonacci_zero_one_eq_fib](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GibonacciNumber.lean)
-/
@[path]
private lemma gibonacci_zero_one_eq_fib_eq
  {n : ℕ} :
-- imply
  gibonacciNumber 0 1 n = (Nat.fib n : ℤ) := by
-- proof
  apply MetaMathlibExt.gibonacci_zero_one_eq_fib n


-- created on 2026-10-20
