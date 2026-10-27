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
import Theorem.RingTheory.LaurentSeries.Part4
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

/-- Prepend a digit to a representation, scaling by 3. -/
def prependDigit (d : BalancedTernaryDigit) {m : ℤ}
    (r : BalancedTernaryRepresentation m) :
    BalancedTernaryRepresentation (d.toInt + 3 * m) where
  digits := prependDigits d r.digits
  finite_support := prependDigits_finite_support d r.digits r.finite_support
  sum_eq := by rw [prependDigits_sum d r.digits r.finite_support, r.sum_eq]

/-! ## Doubly Infinite Power Series

The K-module K[[x^±]] of all families (a_n)_{n ∈ ℤ} of elements of K.
This is the largest space allowing negative powers of x, but it does not
have a well-defined multiplication in general.

This corresponds to Definition `def.fps.laure.double`.
-/


/-- The K-module of doubly infinite power series K[[x^±]].

An element is a family `(a_n)_{n ∈ ℤ}` of elements of K. Addition and scalar
multiplication are defined entrywise.

Note: This is NOT a ring because multiplication is not always well-defined
(the convolution sum may be infinite).

This corresponds to Definition `def.fps.laure.double`.
-/
def DoublyInfinitePowerSeries (K : Type*) [Semiring K] := ℤ → K

end AlgebraicCombinatorics
end
