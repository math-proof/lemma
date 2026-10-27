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
import Structure.RingTheory.HahnSeries.LaurentSeries
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

section BalancedTernaryRepresentation

open Finset

/-- The value of a finitely supported balanced ternary representation. -/
def balancedTernaryValue (f : ℕ →₀ ℤ) : ℤ :=
  ∑ i ∈ f.support, f i * (3 : ℤ) ^ i

/-- A k-bounded balanced ternary representation is a function `f : Fin (k+1) → {-1, 0, 1}`.

These are representations where `f(i) = 0` for all `i > k`. -/
def kBoundedBTReps (k : ℕ) : Finset (Fin (k + 1) → ℤ) :=
  Fintype.piFinset (fun _ => btDigits)

/-- The value of a k-bounded balanced ternary representation. -/
def kBoundedBTValue (k : ℕ) (f : Fin (k + 1) → ℤ) : ℤ :=
  ∑ i : Fin (k + 1), f i * (3 : ℤ) ^ (i : ℕ)

/-- The maximum absolute value representable with k+1 balanced ternary digits:
    `M_k = 3^0 + 3^1 + ... + 3^k = (3^{k+1} - 1) / 2` -/
def maxBT (k : ℕ) : ℕ := ∑ i ∈ range (k + 1), 3 ^ i

/-- The set of integers from -M to M. -/
def Icc_symm (M : ℕ) : Finset ℤ := Icc (-(M : ℤ)) (M : ℤ)

/-- Helper to convert a k-bounded representation to a Finsupp. -/
noncomputable def kBoundedToFinsupp (k : ℕ) (f : Fin (k + 1) → ℤ) : ℕ →₀ ℤ :=
  Finsupp.onFinset (range (k + 1)) (fun i => if h : i < k + 1 then f ⟨i, h⟩ else 0)
    (fun i hi => by
      simp only [mem_range, ne_eq] at hi ⊢
      by_contra h
      push Not at h
      exact hi (dif_neg (not_lt.mpr h)))

end BalancedTernaryRepresentation
end AlgebraicCombinatorics.FPS.Laurent
end
