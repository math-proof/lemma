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
import Def.RingTheory.LaurentSeries.Part8
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

/-! ### Part 1: K[x^±] is a commutative K-algebra

The Laurent polynomial ring K[x^±] is a commutative semiring (and a commutative ring
when K is a ring). It is also a K-algebra.

In Mathlib, this is established via `AddMonoidAlgebra.instCommSemiring` and related instances.
-/


/-- Laurent polynomials form a commutative semiring.
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
instance laurentPolynomial_commSemiring : CommSemiring K[T;T⁻¹] := inferInstance

/-- Laurent polynomials form a K-algebra.
This is part of Theorem `thm.fps.laure.laupol-ring`. -/
instance laurentPolynomial_algebra : Algebra K K[T;T⁻¹] := inferInstance

end LaurentPolynomials
end AlgebraicCombinatorics
end
