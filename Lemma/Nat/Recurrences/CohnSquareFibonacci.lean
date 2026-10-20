import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.CohnSquareFibonacci
open MetaMathlibExt


/--
[cohn_square_fibonacci](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CohnSquareFibonacci.lean)
-/
@[path]
private lemma cohn_square_fibonacci_eq
  {n x : ℕ}
-- given
  (hn : 0 < n)
  (h : Nat.fib n = x ^ 2) :
-- imply
  n = 1 ∨ n = 2 ∨ n = 12 := by
-- proof
  apply MetaMathlibExt.cohn_square_fibonacci n x hn h


-- created on 2026-10-20
