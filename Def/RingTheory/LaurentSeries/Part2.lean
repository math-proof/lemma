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
import Theorem.RingTheory.LaurentSeries
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

/-- The shifted representation gives a representation of n / 2. -/
def BinaryRepresentation.shift {n : ℕ} (r : BinaryRepresentation n) :
    BinaryRepresentation (n / 2) where
  bits := fun i => r.bits (i + 1)
  finite_support := by
    have h := r.finite_support
    have hsub : {i | r.bits (i + 1) ≠ 0} ⊆ Nat.pred '' {i | r.bits i ≠ 0} := by
      intro i hi
      simp only [Set.mem_ofPred_eq, ne_eq] at hi
      simp only [Set.mem_image, Set.mem_ofPred_eq, ne_eq]
      use i + 1, hi
      rfl
    exact Set.Finite.subset (h.image _) hsub
  sum_eq := by
    have h := r.sum_eq
    have hb0 := bits_zero_eq_mod n r
    have hlt : (r.bits 0 : ℕ) < 2 := (r.bits 0).isLt
    have hdecomp := sum_decomposition r.bits r.finite_support
    have heq : n = (r.bits 0 : ℕ) + 2 * (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := by
      calc n = ∑ᶠ i, (r.bits i : ℕ) * 2^i := h.symm
           _ = (r.bits 0 : ℕ) + 2 * (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := hdecomp
    have hdiv2 : n / 2 = (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := by
      calc n / 2 = ((r.bits 0 : ℕ) + 2 * (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i)) / 2 := by rw [← heq]
           _ = (∑ᶠ i, (r.bits (i + 1) : ℕ) * 2^i) := by
               rw [Nat.add_mul_div_left _ _ (by omega : 0 < 2)]
               simp only [Nat.div_eq_of_lt hlt, Nat.zero_add]
    exact hdiv2.symm

end AlgebraicCombinatorics
end
