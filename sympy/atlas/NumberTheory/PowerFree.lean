/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PowerFree.lean -/

import Mathlib.Data.Nat.Squarefree

/-!
# Power-free natural numbers

This file formalizes the classical notion of `k`-free natural number from
Dietmann–Marmon, *The density of twins of k-free numbers* (arXiv `1307.2481v2`):
for `k ≥ 2`, a positive integer is `k`-free when it is not divisible by the
`k`-th power of any prime.

We prove that divisors of a power-free number are power-free at the same level,
monotonicity in the exponent, and that `2`-free is exactly squarefree.
-/

namespace Nat

/-- A natural number `n` is `k`-free if `2 ≤ k`, `0 < n`, and no prime
`k`-th power divides `n`. -/
def IsPowerFree (n k : ℕ) : Prop :=
  2 ≤ k ∧ 0 < n ∧ ∀ p : ℕ, p.Prime → ¬p ^ k ∣ n
end Nat
