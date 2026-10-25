/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EgyptianFraction.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
open scoped BigOperators

/-!
# Egyptian underapproximations

This module records the two denominator-order conventions for finite Egyptian
underapproximations from Kovač–Tang: nondecreasing denominators
(repetitions allowed) and strictly increasing denominators (distinct
denominators), together with the strict-underapproximation condition
`∑ 1/a_i < λ`.

## Main definitions

* `EgyptianFraction.IsNondecreasingEgyptian` membership in `𝓔ₙ^≤`
* `EgyptianFraction.IsStrictEgyptian` membership in `𝓔ₙ^<`
* `EgyptianFraction.IsNondecreasingUnderapproximation`
* `EgyptianFraction.IsStrictUnderapproximation`

## References

* V. Kovač and Q. Tang, *Eventually greedy best Egyptian underapproximations of rational
  numbers via optimal control*, [arXiv:2607.28387v2](https://arxiv.org/abs/2607.28387v2),
  lines 103–120. The superscripts `≤` and `<` in the paper correspond to
  nondecreasing and strictly increasing denominator tuples respectively; for
  `λ > 0` and `σ ∈ {≤, <}`,
  `Rₙ^σ(λ) = max {∑ 1/aᵢ : (a₁,…,aₙ) ∈ 𝓔ₙ^σ, ∑ 1/aᵢ < λ}`.
-/


namespace EgyptianFraction

/-- Membership in `𝓔ₙ^≤` from Kovač–Tang, lines 103–107:
a tuple of natural numbers with `2 ≤ a₁ ≤ ⋯ ≤ aₙ`. -/
def IsNondecreasingEgyptian {n : ℕ} (a : Fin n → ℕ) : Prop :=
  (∀ i, 2 ≤ a i) ∧ Monotone a

/-- Membership in `𝓔ₙ^<` from Kovač–Tang, lines 108–110:
a tuple of natural numbers with `2 ≤ a₁ < ⋯ < aₙ`. -/
def IsStrictEgyptian {n : ℕ} (a : Fin n → ℕ) : Prop :=
  (∀ i, 2 ≤ a i) ∧ StrictMono a

/-- A strict underapproximation by unit fractions whose denominators may repeat
and are presented in nondecreasing order. This is the condition
`(a₁,…,aₙ) ∈ 𝓔ₙ^≤` and `∑ 1/aᵢ < λ` from lines 113–120, together with
`n ≥ 1` and `λ > 0` as in the paper's `ℕ = {1,2,…}` and `λ > 0` setup. -/
def IsNondecreasingUnderapproximation {n : ℕ} (target : ℝ) (a : Fin n → ℕ) : Prop :=
  0 < n ∧
    0 < target ∧
    IsNondecreasingEgyptian a ∧
    ∑ i, ((a i : ℝ)⁻¹) < target

/-- A strict underapproximation by distinct unit fractions, presented with
strictly increasing denominators. This is the condition
`(a₁,…,aₙ) ∈ 𝓔ₙ^<` and `∑ 1/aᵢ < λ` from lines 113–120, with `n ≥ 1`
and `λ > 0`. -/
def IsStrictUnderapproximation {n : ℕ} (target : ℝ) (a : Fin n → ℕ) : Prop :=
  0 < n ∧
    0 < target ∧
    IsStrictEgyptian a ∧
    ∑ i, ((a i : ℝ)⁻¹) < target

end EgyptianFraction
