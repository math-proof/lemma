import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.FibonacciPrimitiveDivisor
open scoped BigOperators
open MetaMathlibExt


/--
[exists_isPrimitiveDivisor_fib](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/FibonacciPrimitiveDivisor.lean)
-/
@[path]
private lemma exists_isPrimitiveDivisor_fib_eq
  {n : Nat}
-- given
  (hn : 7 ≤ n)
  (hne : n ≠ 12) :
-- imply
  ∃ p, LucasSequence.IsPrimitiveDivisor (fun k => (Nat.fib k : Int)) (5 : Int) n p := by
-- proof
  apply MetaMathlibExt.exists_isPrimitiveDivisor_fib hn hne


-- created on 2026-10-20
