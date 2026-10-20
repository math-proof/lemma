import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.CohnTwiceSquareFibonacci
open MetaMathlibExt


/--
[cohn_twice_square_fibonacci](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnTwiceSquareFibonacci.lean)
-/
@[path]
private lemma cohn_twice_square_fibonacci_eq
  {n x : ℕ}
-- given
  (hn : 0 < n)
  (h : Nat.fib n = 2 * x ^ 2) :
-- imply
  n = 3 ∨ n = 6 := by
-- proof
  apply MetaMathlibExt.cohn_twice_square_fibonacci n x hn h


-- created on 2026-10-20
