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
import Def.RingTheory.LaurentSeries.Part7
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

/-- For ℤ, a set bounded below is partially well-ordered.

This follows from the fact that any sequence in ℤ bounded below has a monotone
subsequence (by Ramsey's theorem / infinite pigeonhole). -/
theorem Int.isPWO_of_bddBelow {s : Set ℤ} (hs : BddBelow s) : s.IsPWO := by
  obtain ⟨N, hN⟩ := hs
  rw [Set.isPWO_iff_exists_monotone_subseq]
  intro g hg
  -- g : ℕ → ℤ with values in s
  -- Consider h : ℕ → ℕ defined by h(n) = (g(n) - N).toNat
  let h : ℕ → ℕ := fun n => (g n - N).toNat
  -- Any sequence in ℕ has a monotone or antitone subsequence (Ramsey)
  have ⟨φ, hφ⟩ := exists_increasing_or_nonincreasing_subseq (α := ℕ) (r := (· ≤ ·)) h
  rcases hφ with hφ_mono | hφ_anti
  · -- Increasing case
    use φ
    intro i j hij
    have hi := hg (φ i)
    have hj := hg (φ j)
    have hNi : N ≤ g (φ i) := hN hi
    have hNj : N ≤ g (φ j) := hN hj
    rcases hij.lt_or_eq with hij' | rfl
    · have hmono := hφ_mono i j hij'
      simp only [h] at hmono
      have h1 : 0 ≤ g (φ i) - N := by omega
      have h2 : 0 ≤ g (φ j) - N := by omega
      have h3 : (g (φ i) - N).toNat ≤ (g (φ j) - N).toNat := hmono
      have h4 : g (φ i) - N ≤ g (φ j) - N := by
        calc g (φ i) - N = ((g (φ i) - N).toNat : ℤ) := (Int.toNat_of_nonneg h1).symm
          _ ≤ ((g (φ j) - N).toNat : ℤ) := by exact_mod_cast h3
          _ = g (φ j) - N := Int.toNat_of_nonneg h2
      -- Now we need g (φ i) ≤ g (φ j), which follows from h4
      have : g (φ i) ≤ g (φ j) := by linarith
      exact this
    · rfl
  · -- Non-increasing (decreasing) case
    -- In ℕ, a strictly decreasing sequence can't exist infinitely
    exfalso
    -- Build a strictly decreasing sequence in ℕ
    have hdec : ∀ m n, m < n → h (φ n) < h (φ m) := fun m n hmn => by
      have := hφ_anti m n hmn
      omega
    -- Infinite strictly decreasing sequence in ℕ is impossible
    -- h(φ 0) > h(φ 1) > h(φ 2) > ... but all are ≥ 0
    have : ∀ n, h (φ n) + n ≤ h (φ 0) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        have hk := hdec k (k + 1) (Nat.lt_succ_self k)
        omega
    have := this (h (φ 0) + 1)
    omega

end DoublyInfinitePowerSeries
end AlgebraicCombinatorics
end
