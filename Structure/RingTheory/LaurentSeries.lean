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

/-! ## Binary Representation

A binary representation encodes a nonnegative integer as an essentially finite
sequence of bits (0 or 1).
-/


/-- A binary representation of a nonnegative integer `n` is an essentially finite
sequence `(b_i)_{i ∈ ℕ}` of elements in `{0, 1}` such that `n = ∑ b_i * 2^i`.

This corresponds to Definition in `sec.gf.laure` of the source.
-/
structure BinaryRepresentation (n : ℕ) where
  /-- The sequence of bits -/
  bits : ℕ → Fin 2
  /-- Only finitely many bits are nonzero -/
  finite_support : {i | bits i ≠ 0}.Finite
  /-- The sum equals n -/
  sum_eq : ∑ᶠ i, (bits i : ℕ) * 2^i = n

end AlgebraicCombinatorics
end
