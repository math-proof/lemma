/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/PrimitiveDivisor.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

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

open scoped BigOperators

namespace LucasSequence

/-- A prime `p` is a primitive divisor of `u n` when it divides `u n` but not
the discriminant times the product `u 1 * ... * u (n - 1)`. -/
def IsPrimitiveDivisor (u : ℕ → ℤ) (discriminant : ℤ) (n p : ℕ) : Prop :=
  0 < n ∧ p.Prime ∧ (p : ℤ) ∣ u n ∧
    ¬(p : ℤ) ∣ discriminant * ∏ k ∈ Finset.Ico 1 n, u k

theorem IsPrimitiveDivisor.pos {u : ℕ → ℤ} {discriminant : ℤ} {n p : ℕ}
    (h : IsPrimitiveDivisor u discriminant n p) : 0 < n :=
  h.1

theorem IsPrimitiveDivisor.prime {u : ℕ → ℤ} {discriminant : ℤ} {n p : ℕ}
    (h : IsPrimitiveDivisor u discriminant n p) : p.Prime :=
  h.2.1

theorem IsPrimitiveDivisor.dvd_term {u : ℕ → ℤ} {discriminant : ℤ} {n p : ℕ}
    (h : IsPrimitiveDivisor u discriminant n p) : (p : ℤ) ∣ u n :=
  h.2.2.1

theorem IsPrimitiveDivisor.not_dvd_badPart {u : ℕ → ℤ}
    {discriminant : ℤ} {n p : ℕ} (h : IsPrimitiveDivisor u discriminant n p) :
    ¬(p : ℤ) ∣ discriminant * ∏ k ∈ Finset.Ico 1 n, u k :=
  h.2.2.2

theorem IsPrimitiveDivisor.not_dvd_discriminant {u : ℕ → ℤ}
    {discriminant : ℤ} {n p : ℕ} (h : IsPrimitiveDivisor u discriminant n p) :
    ¬(p : ℤ) ∣ discriminant := by
  intro hp
  exact h.not_dvd_badPart (dvd_mul_of_dvd_left hp _)

theorem IsPrimitiveDivisor.not_dvd_prior {u : ℕ → ℤ} {discriminant : ℤ}
    {n p k : ℕ} (h : IsPrimitiveDivisor u discriminant n p)
    (hk : k ∈ Finset.Ico 1 n) : ¬(p : ℤ) ∣ u k := by
  intro hp
  apply h.not_dvd_badPart
  exact dvd_mul_of_dvd_right (dvd_trans hp (Finset.dvd_prod_of_mem u hk)) _

end LucasSequence
