/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Copyright (c) 2025 AlgebraicCombinatorics contributors. All rights reserved.
Authors: AlgebraicCombinatorics contributors
-/
import Mathlib
import Def.RingTheory.LaurentSeries.Part11
import Lemma.PowerSeries.InfiniteProducts2
import Lemma.LaurentSeries.LaurentSeries
import Lemma.Partition.NPartition
import Theorem.RingTheory.HahnSeries.LaurentSeries.Part2
open scoped LaurentPolynomial Polynomial
open LaurentPolynomial HahnSeries

/-!
# Laurent Power Series

This file formalizes properties of Laurent polynomials and Laurent power series,
following Section `\ref{sec.details.gf.laure}` of the source material.

## Overview

Laurent polynomials are formal sums `∑_{i ∈ ℤ} aᵢ xⁱ` where only finitely many coefficients
are nonzero. Laurent power series are formal sums where the sequence of negative-indexed
coefficients is essentially finite (i.e., only finitely many negative powers appear).

In Mathlib:
- Laurent polynomials are `LaurentPolynomial R` (notation `R[T;T⁻¹]`), implemented as
  `AddMonoidAlgebra R ℤ`
- Laurent series are `LaurentSeries R` (notation `R⸨X⸩`), implemented as `HahnSeries ℤ R`

## Main Results

### Laurent Polynomials (Theorem thm.fps.laure.laupol-ring)
- `LaurentPolynomial` forms a commutative `K`-algebra with `x` invertible
- Multiplication by `x` shifts coefficients: `x · a = (aₙ₋₁)_{n∈ℤ}` (Lemma lem.fps.laure.xa)
- For each `k ∈ ℤ`, we have `xᵏ = (δᵢ,ₖ)_{i∈ℤ}` (Proposition prop.fps.laure.xk)
- Every Laurent polynomial can be written as `∑ aᵢ xⁱ` (`eq_sum_T`)

### Laurent Series (Theorem thm.fps.laure.lauser-ring)
- `LaurentSeries` forms a commutative `K`-algebra with `x` invertible
- The product of two Laurent series is again a Laurent series (closure under multiplication)
- Every Laurent series can be written as `∑_{i∈ℤ} aᵢ xⁱ` (Proposition prop.fps.laure.a=sumaixi)

## References

- Source: `AlgebraicCombinatorics/tex/Details/LaurentSeries.tex`
- Labels: `thm.fps.laure.laupol-ring`, `lem.fps.laure.xa`, `prop.fps.laure.xk`,
  `prop.fps.laure.a=sumaixi`, `thm.fps.laure.lauser-ring`
-/


-- `AddMonoidAlgebra` is a wrapper around `M →₀ R` (`coeff`), not the `Finsupp` itself.


noncomputable section

namespace AlgebraicCombinatorics.FPS.Laurent

section BalancedTernaryEquivalence

/-- Convert a `BTRep` (inductive style from `LaurentSeries.lean`) 
to a `BalancedTernaryRep` (Finsupp style). -/
noncomputable def BTRep.toFinsupp {n : ℤ} (r : BTRep n) : BalancedTernaryRep n where
  digits := {
    support := r.finite_support.toFinset
    toFun := fun i => (r.digits i).toInt
    mem_support_toFun := by
      intro i
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq,
                 AlgebraicCombinatorics.BalancedTernaryDigit.ne_zero_iff_toInt_ne_zero, ne_eq]
  }
  digits_range := fun i => BTDigit.toInt_mem_btDigits _
  sum_eq := by
    simp only [Finsupp.coe_mk]
    have h := r.sum_eq
    rw [finsum_eq_sum_of_support_subset _ (s := r.finite_support.toFinset)] at h
    · convert h using 1
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      simp only [Set.Finite.coe_toFinset, Set.mem_ofPred_eq]
      intro heq
      apply hi
      simp only [heq, AlgebraicCombinatorics.BalancedTernaryDigit.toInt_zero, zero_mul]

/-- Convert a `BalancedTernaryRep` (Finsupp style) to a 
`BTRep` (inductive style from `LaurentSeries.lean`). -/
noncomputable def BalancedTernaryRep.toInductive {n : ℤ} (r : BalancedTernaryRep n) : BTRep n where
  digits := fun i => btDigitOfInt (r.digits i)
  finite_support := by
    have h : {i | btDigitOfInt (r.digits i) ≠ 0} ⊆ r.digits.support := by
      intro i hi
      simp only [Set.mem_ofPred_eq] at hi
      simp only [Finset.mem_coe, Finsupp.mem_support_iff]
      rw [btDigitOfInt_ne_zero_iff _ (r.digits_range i)] at hi
      exact hi
    exact r.digits.support.finite_toSet.subset h
  sum_eq := by
    have h := r.sum_eq
    rw [finsum_eq_sum_of_support_subset _ (s := r.digits.support)]
    · convert h using 2 with i _
      rw [btDigitOfInt_toInt _ (r.digits_range i)]
    · intro i hi
      simp only [Function.mem_support, ne_eq] at hi
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro hz
      apply hi
      rw [hz, btDigitOfInt_zero]
      simp [AlgebraicCombinatorics.BalancedTernaryDigit.toInt]

end BalancedTernaryEquivalence
end AlgebraicCombinatorics.FPS.Laurent
end
