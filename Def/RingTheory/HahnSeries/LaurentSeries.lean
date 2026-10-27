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


namespace AddMonoidAlgebra

variable {R M : Type*} [Semiring R]

def support (x : AddMonoidAlgebra R M) : Finset M := x.coeff.support

end AddMonoidAlgebra
