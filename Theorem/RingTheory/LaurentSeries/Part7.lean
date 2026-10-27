/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2024 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
import Lemma.PowerSeries.InfiniteProducts2
import Lemma.Partition.NPartition
import Instance.RingTheory.LaurentSeries.Part3
open scoped LaurentPolynomial

/-!
# Laurent Power Series

This file formalizes the content from Section `sec.gf.laure` of the textbook,
covering Laurent power series and related concepts.

## Main Definitions

* `BinaryRepresentation` - A binary representation of a nonnegative integer
* `BalancedTernaryRepresentation` - A balanced ternary representation of an integer
* `DoublyInfinitePowerSeries` - The K-module K[[x^±]] of all families indexed by ℤ
* `DoublyInfinitePowerSeries.IsLaurentSeries` - Predicate for when a doubly infinite
  power series is a Laurent series (Definition `def.fps.laure.lauser`)
* We also use Mathlib's `LaurentPolynomial` for K[x^±] and `LaurentSeries` for K((x))

## Main Results

* `binaryRepresentation_unique` - Each n ∈ ℕ has a unique binary representation
* `balancedTernaryRepresentation_unique` - Each integer has a unique balanced ternary representation
* `isLaurentSeries_ofLaurentSeries` - Mathlib's LaurentSeries satisfies our IsLaurentSeries predicate
* `toLaurentSeries_ofLaurentSeries` / `ofLaurentSeries_toLaurentSeries` - Round-trip equivalence
  showing our definition matches Mathlib's
* `Int.isPWO_of_bddBelow` - Bounded below subsets of ℤ are partially well-ordered
* Properties of Laurent polynomials and Laurent series from Mathlib

## References

* [Grinberg, *Algebraic Combinatorics*], Section on Laurent power series
-/


noncomputable section

namespace AlgebraicCombinatorics

section LaurentPolynomials

variable (K : Type*) [CommSemiring K]

/-! ### Part 2: The unity is (δ_{i,0})_{i∈ℤ}

The multiplicative identity in K[x^±] is the family that is 1 at index 0 and 0 elsewhere.
In Mathlib, this is `LaurentPolynomial.T 0 = 1`.
-/
/-! ### Part 3: The element x is invertible

The element x (represented as T 1 in Mathlib) is a unit in K[x^±], with inverse x⁻¹ = T (-1).
-/

/-- The inverse of T n is T (-n).
This is the explicit inverse formula from Theorem `thm.fps.laure.laupol-ring`. -/
@[simp]
theorem laurentPolynomial_T_mul_T_neg (n : ℤ) :
    (LaurentPolynomial.T n : K[T;T⁻¹]) * LaurentPolynomial.T (-n) = 1 := by
  rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]

/-- The inverse of T n is T (-n) (multiplication in the other order).
This is the explicit inverse formula from Theorem `thm.fps.laure.laupol-ring`. -/
@[simp]
theorem laurentPolynomial_T_neg_mul_T (n : ℤ) :
    (LaurentPolynomial.T (-n) : K[T;T⁻¹]) * LaurentPolynomial.T n = 1 := by
  rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]

end LaurentPolynomials
end AlgebraicCombinatorics
end
