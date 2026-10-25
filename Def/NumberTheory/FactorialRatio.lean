/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/FactorialRatio.lean -/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Choose.Basic


/-!
# Integral factorial ratios

This file introduces the reusable predicate needed to state the classification
problem of K. Soundararajan's *Integral factorial ratios* (arXiv `1901.05133v1`,
`Factorials6.tex`, lines 83-91): for tuples of positive naturals `A = [a₁, …, aₖ]`
and `B = [b₁, …, bₗ]` with equal sums, the quotient
`(a₁n)! ⋯ (aₖn)! / ((b₁n)! ⋯ (bₗn)!)` is a natural number for every `n`.

The quotient is formalized through divisibility in `ℕ`: the denominator product
divides the numerator product. The `n = 0` case is automatic since every
factorial there equals one.

## Main declarations

* `factorialProd`: product of scaled factorials over a tuple at index `n`.
* `IsIntegralFactorialRatio`: the integral factorial-ratio predicate.
-/

/-- Product of the scaled factorials `(a * n)!` over the entries `a` of `L`. -/
def factorialProd (L : List ℕ) (n : ℕ) : ℕ :=
  (L.map fun a => Nat.factorial (a * n)).prod

/-- The integral factorial-ratio predicate from *Integral factorial ratios*:
both tuples consist of positive naturals, their sums agree (the paper's balance
condition `∑ aᵢ = ∑ bⱼ`), and the denominator product divides the numerator
product at every index `n`. -/
def IsIntegralFactorialRatio (A B : List ℕ) : Prop :=
  (∀ a ∈ A, 0 < a) ∧ (∀ b ∈ B, 0 < b) ∧ A.sum = B.sum ∧
    ∀ n : ℕ, factorialProd B n ∣ factorialProd A n

