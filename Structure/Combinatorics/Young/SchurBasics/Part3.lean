/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
import Theorem.Combinatorics.Young.SchurBasics.Part4
/-!
# Schur Polynomials

This file formalizes the basics of Schur polynomials, including:
- Alternants and the ρ vector
- Young diagrams for N-partitions
- Semistandard Young tableaux (SSYT)
- Schur polynomials as sums over SSYT
- Skew Young diagrams and skew Schur polynomials

The main result is that Schur polynomials are symmetric (Theorem `thm.sf.schur-symm` and
`thm.sf.skew-schur-symm` in the source).

## Main Definitions

- `NPartition N`: An N-partition is an N-tuple of natural numbers that is weakly decreasing
- `rhoVector N`: The N-tuple (N-1, N-2, ..., 0)
- `alternant α`: The alternant a_α = det(x_i^{α_j})
- `NPartition.youngDiagram`: The Young diagram Y(λ) of an N-partition λ
- `SSYT`: Semistandard Young tableaux of shape λ
- `schurPoly`: The Schur polynomial s_λ
- `SkewYoungDiagram`: Skew Young diagrams Y(λ/μ)
- `skewSchurPoly`: The skew Schur polynomial s_{λ/μ}

## References

Based on the LaTeX source `AlgebraicCombinatorics/tex/SymmetricFunctions/SchurBasics.tex`

## Tags

Schur polynomial, Young diagram, semistandard tableau, alternant, symmetric polynomial
-/


noncomputable section

open Finset Matrix Polynomial MvPolynomial BigOperators

open scoped Classical

variable (N : ℕ) [NeZero N]

variable {R : Type*} [CommRing R]

/-! ## Skew Young Tableaux -/


/-- A skew Young tableau of shape λ/μ is a filling of Y(λ/μ) with elements of [N].
    Definition \ref{def.sf.skew-tab} in the source.

    Formally, a Young tableau of shape λ/μ is a map T : Y(λ/μ) → [N].
    We represent this as a total function `entry : Fin N × ℕ → Fin N` with a support
    condition that entries outside the skew diagram are 0.

    Young tableaux of shape λ/μ are often called "skew Young tableaux".

    Note: If μ ⊈ λ (i.e., not μ ≤ λ), then there are no Young tableaux of shape λ/μ
    because the skew diagram would be empty or malformed. -/
structure SkewYoungTableau {N : ℕ} [NeZero N] (lam mu : NPartition N) where
  /-- The filling function T : Y(λ/μ) → [N] -/
  entry : Fin N × ℕ → Fin N
  /-- The entry is only meaningful for cells in the skew diagram -/
  support : ∀ c, c ∉ skewYoungDiagram lam mu → entry c = 0

end
