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
import Theorem.RingTheory.LaurentSeries.Part9
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

/-! ## Partial Product Formula

The key computation used to prove Theorem `thm.fps.laure.balanced-tern-rep-uniq`
involves the partial products ∏_{i=0}^{k} (1 + x^{3^i} + x^{-3^i}).
-/


/-- The partial product ∏_{i=0}^{k} (1 + T^{3^i} + T^{-3^i}) in the Laurent polynomial ring.
This is used in the proof of Theorem `thm.fps.laure.balanced-tern-rep-uniq`. -/
def balancedTernaryPartialProduct (K : Type*) [CommSemiring K] (k : ℕ) : K[T;T⁻¹] :=
  ∏ i ∈ Finset.range (k + 1),
    (1 + LaurentPolynomial.T ((3 : ℤ)^i) + LaurentPolynomial.T (-((3 : ℤ)^i)))

end AlgebraicCombinatorics
end
