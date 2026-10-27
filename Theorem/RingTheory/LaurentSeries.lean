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
import Def.RingTheory.LaurentSeries
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

/-- Helper: the support of bits i * 2^i is contained in the support of bits. -/
theorem support_mul_pow_subset (bits : ℕ → Fin 2) :
    {i : ℕ | (bits i : ℕ) * 2^i ≠ 0} ⊆ {i | bits i ≠ 0} := by
  intro i hi
  simp only [Set.mem_ofPred_eq, ne_eq] at hi ⊢
  intro h
  apply hi
  simp [h]

/-- The least significant bit equals n mod 2. -/
theorem bits_zero_eq_mod (n : ℕ) (r : BinaryRepresentation n) : (r.bits 0 : ℕ) = n % 2 := by
  have h := r.sum_eq
  have hfin : {i : ℕ | (r.bits i : ℕ) * 2^i ≠ 0}.Finite :=
    r.finite_support.subset (support_mul_pow_subset r.bits)
  have hdiv : ∀ i : ℕ, i ≥ 1 → 2 ∣ (r.bits i : ℕ) * 2^i := by
    intro i hi
    have : 2 ∣ 2^i := dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hi)
    exact Dvd.dvd.mul_left this (r.bits i : ℕ)
  have h_mod : (∑ᶠ i, (r.bits i : ℕ) * 2^i) % 2 = (r.bits 0 : ℕ) % 2 := by
    rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) (f := fun i => (r.bits i : ℕ) * 2^i)]
    · by_cases h0 : 0 ∈ hfin.toFinset
      · rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem h0]
        simp only [pow_zero, mul_one]
        have hsum_div : 2 ∣ ∑ i ∈ hfin.toFinset \ {0}, (r.bits i : ℕ) * 2 ^ i := by
          apply Finset.dvd_sum
          intro i hi
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hi
          exact hdiv i (Nat.one_le_iff_ne_zero.mpr hi.2)
        have : (∑ i ∈ hfin.toFinset \ {0}, (r.bits i : ℕ) * 2 ^ i) % 2 = 0 :=
          Nat.mod_eq_zero_of_dvd hsum_div
        omega
      · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, pow_zero, mul_one, ne_eq,
                   not_not] at h0
        have hsum_div : 2 ∣ ∑ i ∈ hfin.toFinset, (r.bits i : ℕ) * 2 ^ i := by
          apply Finset.dvd_sum
          intro i hi
          simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, ne_eq] at hi
          have hne : i ≠ 0 := by
            intro heq
            subst heq
            simp only [pow_zero, mul_one] at hi h0
            exact hi h0
          exact hdiv i (Nat.one_le_iff_ne_zero.mpr hne)
        have hsum_zero : (∑ i ∈ hfin.toFinset, (r.bits i : ℕ) * 2 ^ i) % 2 = 0 :=
          Nat.mod_eq_zero_of_dvd hsum_div
        simp only [h0, Nat.zero_mod]
        exact hsum_zero
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      exact hfin.mem_toFinset.mpr hi
  rw [h] at h_mod
  have hlt : (r.bits 0 : ℕ) < 2 := (r.bits 0).isLt
  omega

/-- Sum decomposition: ∑ᶠ i, bits i * 2^i = bits 0 + 2 * ∑ᶠ i, bits (i+1) * 2^i -/
theorem sum_decomposition (bits : ℕ → Fin 2) (hfin : {i | bits i ≠ 0}.Finite) :
    ∑ᶠ i, (bits i : ℕ) * 2^i = (bits 0 : ℕ) + 2 * (∑ᶠ i, (bits (i + 1) : ℕ) * 2^i) := by
  -- First rewrite the LHS as sum over {0} plus sum over positive naturals
  have huniv : (Set.univ : Set ℕ) = {0} ∪ Set.range Nat.succ := by
    ext n
    simp only [Set.mem_univ, Set.mem_union, Set.mem_singleton_iff, Set.mem_range, true_iff]
    cases n with
    | zero => left; rfl
    | succ n => right; exact ⟨n, rfl⟩
  -- Helper lemma: (bits i : ℕ) = 0 iff bits i = 0
  have hval_zero : ∀ i, (bits i : ℕ) = 0 ↔ bits i = 0 := by
    intro i
    constructor
    · intro h
      exact Fin.val_injective h
    · intro h
      simp [h]
  -- The support is finite
  have hsup : (Function.support (fun i => (bits i : ℕ) * 2^i)).Finite := by
    apply hfin.subset
    intro i hi
    simp only [Function.mem_support, ne_eq, Set.mem_ofPred_eq] at hi ⊢
    intro hb
    apply hi
    simp [hb]
  -- Rewrite as finsum over univ
  rw [← finsum_mem_univ (f := fun i => (bits i : ℕ) * 2^i)]
  rw [huniv]
  -- Split the union
  rw [finsum_mem_union']
  · -- Simplify the singleton sum
    simp only [finsum_mem_singleton, pow_zero, mul_one]
    congr 1
    -- The sum over range Nat.succ equals the shifted sum
    rw [finsum_mem_range Nat.succ_injective]
    -- Now we have ∑ᶠ j, bits (j + 1) * 2^(j + 1)
    -- Need to show this equals 2 * ∑ᶠ i, bits (i + 1) * 2^i
    have hfin_shift : (Function.support (fun i => (bits (i + 1) : ℕ) * 2^i)).Finite := by
      have hsub : Function.support (fun i => (bits (i + 1) : ℕ) * 2^i) ⊆
                  Nat.pred '' {i | bits i ≠ 0} := by
        intro i hi
        simp only [Function.mem_support, ne_eq] at hi
        simp only [Set.mem_image, Set.mem_ofPred_eq]
        use i + 1
        constructor
        · intro hb
          apply hi
          simp [hb]
        · simp
      exact (hfin.image _).subset hsub
    -- We have ∑ᶠ j, bits (j.succ) * 2^(j.succ) = ∑ᶠ j, bits (j + 1) * 2^(j + 1)
    -- And we want 2 * ∑ᶠ i, bits (i + 1) * 2^i
    -- Note that bits (j + 1) * 2^(j + 1) = 2 * bits (j + 1) * 2^j
    have heq : ∀ j, (bits j.succ : ℕ) * 2^j.succ = 2 * ((bits (j + 1) : ℕ) * 2^j) := by
      intro j
      simp only [Nat.succ_eq_add_one]
      ring
    conv_lhs =>
      arg 1
      ext j
      rw [heq j]
    -- Now we have ∑ᶠ j, 2 * (bits (j + 1) * 2^j) = 2 * ∑ᶠ i, bits (i + 1) * 2^i
    -- The support of 2 * f is the same as the support of f
    have hsup2 : (Function.support (fun i => 2 * ((bits (i + 1) : ℕ) * 2^i))).Finite := by
      apply hfin_shift.subset
      intro i hi
      simp only [Function.mem_support, ne_eq] at hi ⊢
      intro h
      apply hi
      omega
    have hsupeq : hsup2.toFinset = hfin_shift.toFinset := by
      ext i
      simp only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq]
      constructor
      · intro h1 h2
        apply h1
        omega
      · intro h1 h2
        apply h1
        simp only [mul_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false] at h2
        cases h2 with
        | inl h => exact absurd h (by norm_num)
        | inr h => simp [(hval_zero (i + 1)).mp h]
    rw [finsum_eq_sum _ hsup2, hsupeq]
    calc ∑ i ∈ hfin_shift.toFinset, 2 * ((bits (i + 1) : ℕ) * 2^i)
        = 2 * ∑ i ∈ hfin_shift.toFinset, (bits (i + 1) : ℕ) * 2^i := by rw [Finset.mul_sum]
      _ = 2 * ∑ᶠ i, (bits (i + 1) : ℕ) * 2^i := by rw [← finsum_eq_sum _ hfin_shift]
  · -- Disjoint
    simp only [Set.disjoint_singleton_left, Set.mem_range]
    intro ⟨n, hn⟩
    omega
  · -- Finite intersection for singleton
    exact Set.finite_singleton 0 |>.inter_of_left _
  · -- Finite intersection for range
    apply Set.Finite.subset hsup
    intro i hi
    obtain ⟨_, hi'⟩ := hi
    exact hi'

end AlgebraicCombinatorics
end
