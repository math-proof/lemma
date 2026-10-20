import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.GibonacciSquaresRecurrence
open MetaMathlibExt


/--
[gibonacci_sq_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/GibonacciSquaresRecurrence.lean)
-/
@[path]
private lemma gibonacci_sq_recurrence_eq
  {g : ℕ → ℤ}
  {n : ℕ}
-- given
  (hg : ∀ n : ℕ, g (n + 2) = g (n + 1) + g n) :
-- imply
  g (n + 3) ^ 2 = (Nat.fib 3 : ℤ) * g (n + 2) ^ 2 +
      (Nat.fib 3 : ℤ) * g (n + 1) ^ 2 - g n ^ 2 := by
-- proof
  apply MetaMathlibExt.gibonacci_sq_recurrence g hg n


-- created on 2026-10-20
