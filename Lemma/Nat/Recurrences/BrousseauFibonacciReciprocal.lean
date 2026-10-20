import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.BrousseauFibonacciReciprocal
open scoped BigOperators
open MetaMathlibExt


/--
[brousseau_fibonacci_reciprocal_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/BrousseauFibonacciReciprocal.lean)
-/
@[path]
private lemma brousseau_fibonacci_reciprocal_sum_eq
  {q : ℕ}
-- given
  (hq : 0 < q) :
-- imply
  HasSum
    (fun k : ℕ =>
    ((-1 : ℝ) ^ k * Nat.fib (2 * (k + 1) + q)) /
    ((Nat.fib (k + 1) : ℝ) ^ 2 * (Nat.fib (k + 1 + q) : ℝ) ^ 2))
    ((Nat.fib q : ℝ)⁻¹ *
    ∑ k ∈ Finset.Icc 1 q, ((-1 : ℝ) ^ (k - 1)) / (Nat.fib k : ℝ) ^ 2) := by
-- proof
  apply MetaMathlibExt.brousseau_fibonacci_reciprocal_sum q hq


-- created on 2026-10-20
