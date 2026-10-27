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
import Theorem.RingTheory.LaurentSeries.Part5
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

namespace DoublyInfinitePowerSeries

variable {K : Type*} [Semiring K]

/-- The element x^n in K[[x^±]], represented as a family -/
def single (n : ℤ) : DoublyInfinitePowerSeries K := fun m => if m = n then 1 else 0

/-- A doubly infinite power series is a Laurent series if the sequence of negative
coefficients (a_{-1}, a_{-2}, a_{-3}, ...) is essentially finite, i.e., all
sufficiently negative indices have zero coefficient.

This is Definition `def.fps.laure.lauser` from the textbook:
We let K((x)) be the subset of K[[x^±]] consisting of all families (a_i)_{i∈ℤ}
such that the sequence (a_{-1}, a_{-2}, a_{-3}, ...) is essentially finite --
i.e., such that all sufficiently low i ∈ ℤ satisfy a_i = 0.

The elements of K((x)) are called Laurent series in one indeterminate x over K. -/
def IsLaurentSeries (f : DoublyInfinitePowerSeries K) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, n < N → coeff f n = 0

/-- Convert a Mathlib LaurentSeries to a DoublyInfinitePowerSeries -/
def ofLaurentSeries (f : LaurentSeries K) : DoublyInfinitePowerSeries K :=
  fun n => f.coeff n

end DoublyInfinitePowerSeries
end AlgebraicCombinatorics
end
