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
import Def.RingTheory.LaurentSeries.Part4
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

theorem prependDigits_zero (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit) :
    prependDigits d f 0 = d := rfl

theorem prependDigits_succ (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit)
    (i : ℕ) : prependDigits d f (i + 1) = f i := rfl

theorem prependDigits_finite_support (d : BalancedTernaryDigit)
    (f : ℕ → BalancedTernaryDigit) (hf : {i | f i ≠ 0}.Finite) :
    {i | prependDigits d f i ≠ 0}.Finite := by
  have hsub : {i | prependDigits d f i ≠ 0} ⊆ {0} ∪ Nat.succ '' {i | f i ≠ 0} := by
    intro i hi
    simp only [Set.mem_ofPred_eq, ne_eq] at hi
    cases i with
    | zero => left; exact Set.mem_singleton 0
    | succ i =>
      right
      simp only [Set.mem_image, Set.mem_ofPred_eq, ne_eq]
      use i
      simp [prependDigits] at hi
      exact ⟨hi, rfl⟩
  exact Set.Finite.subset (Set.finite_singleton 0 |>.union (hf.image _)) hsub

theorem prependDigits_sum (d : BalancedTernaryDigit) (f : ℕ → BalancedTernaryDigit)
    (hf : {i | f i ≠ 0}.Finite) :
    ∑ᶠ i, (prependDigits d f i).toInt * (3 : ℤ)^i =
    d.toInt + 3 * ∑ᶠ i, (f i).toInt * (3 : ℤ)^i := by
  let S := {0} ∪ Nat.succ '' (hf.toFinset : Set ℕ)
  have hS_fin : S.Finite := Set.finite_singleton 0 |>.union (Finset.finite_toSet _ |>.image _)
  have hsupp_sub : Function.support (fun i => (prependDigits d f i).toInt * (3 : ℤ)^i) ⊆
      hS_fin.toFinset := by
    intro i hi
    simp only [Function.mem_support, ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      false_and, or_false, Set.Finite.mem_toFinset, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_image, Finset.mem_coe, S] at hi ⊢
    cases i with
    | zero => left; rfl
    | succ i =>
      right; use i; simp [prependDigits] at hi
      refine ⟨?_, rfl⟩
      simp only [Set.mem_ofPred_eq]
      exact (BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero _).mpr hi
  rw [finsum_eq_sum_of_support_subset _ hsupp_sub]
  have hS_eq : hS_fin.toFinset = {0} ∪ (hf.toFinset.image Nat.succ) := by
    ext i; simp [Set.Finite.mem_toFinset, Set.mem_image, Finset.mem_image, S]
  rw [hS_eq]
  have h0_not_in_image : (0 : ℕ) ∉ hf.toFinset.image Nat.succ := by
    simp only [Finset.mem_image, not_exists, not_and]; intro i _ h; omega
  rw [Finset.sum_union (Finset.disjoint_singleton_left.mpr h0_not_in_image)]
  simp only [Finset.sum_singleton, prependDigits_zero, pow_zero, mul_one]
  rw [Finset.sum_image (fun i _ j _ h => Nat.succ_injective h)]
  have hsum_eq : ∑ i ∈ hf.toFinset, (prependDigits d f (i + 1)).toInt * (3 : ℤ)^(i + 1) =
                 ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^(i + 1) := by
    apply Finset.sum_congr rfl; intro i _; simp [prependDigits_succ]
  rw [hsum_eq]
  have hfactor : ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^(i + 1) =
                 3 * ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  rw [hfactor]
  have hfinsum_eq : ∑ᶠ i, (f i).toInt * (3 : ℤ)^i =
      ∑ i ∈ hf.toFinset, (f i).toInt * (3 : ℤ)^i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    simp only [Function.mem_support, ne_eq, mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      false_and, or_false] at hi
    rw [Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    exact (BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero _).mpr hi
  simp only [hfinsum_eq]

end AlgebraicCombinatorics
end
