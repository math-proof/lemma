/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat
open scoped BigOperators

/-!
# Primitive divisors of Lucas-sequence terms

This module isolates the primitive-divisor predicate used for Lucas and related
integer sequences. The discriminant parameter is `(α - β) ^ 2` for a Lucas
pair `(α, β)`.

## References

* Haojie Hong, *On big primitive divisors of Fibonacci numbers*,
  [arXiv:2312.04354v1](https://arxiv.org/abs/2312.04354),
  `bigPFn.tex` lines 153–158 (primitive-divisor definition:
  `p ∣ uₙ` but `p ∤ (α-β)² u₁ ⋯ uₙ₋₁`).
-/


namespace LucasSequence

/-- A prime `p` is a primitive divisor of `u n` when it divides `u n` but not
the discriminant times the product `u 1 * ... * u (n - 1)`. -/
def IsPrimitiveDivisor (u : ℕ → ℤ) (discriminant : ℤ) (n p : ℕ) : Prop :=
  0 < n ∧ p.Prime ∧ (p : ℤ) ∣ u n ∧
    ¬(p : ℤ) ∣ discriminant * ∏ k ∈ Finset.Ico 1 n, u k

end LucasSequence
