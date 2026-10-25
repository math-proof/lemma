/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
import Def.Combinatorics.Young.SchurBasics.Part3
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

/-- A semistandard Young tableau (SSYT) is a tableau where:
    - entries increase weakly along each row (left to right)
    - entries increase strictly down each column (top to bottom)

    Definition \ref{def.sf.ssyt} in the source.

    Formally, a Young tableau T : Y(λ) → [N] is semistandard if and only if:
    - T(i, j) ≤ T(i, j+1) for any (i, j) ∈ Y(λ) with (i, j+1) ∈ Y(λ)
    - T(i, j) < T(i+1, j) for any (i, j) ∈ Y(λ) with (i+1, j) ∈ Y(λ)

    The set of all semistandard Young tableaux of shape λ is denoted SSYT(λ).

    **Note:** This is one of two SSYT definitions in this project:
    - **This definition** (`SchurBasics.SSYT`): Uses `entry : Fin N × ℕ → Fin N` with a support
      condition that entries outside the Young diagram are 0. Extends `YoungTableau`.
      Requires `[NeZero N]`. Field names: `row_weak`, `col_strict`.
    - **Alternative definition** (`SymmetricFunctions.SSYT` in `PieriJacobiTrudi.lean`): Uses
      dependent types `entries : (i : Fin N) → (j : Fin (lam.parts i)) → Fin N`. Standalone
      structure. No `[NeZero N]` requirement. Field names: `rowWeak`, `colStrict`.

    The equivalence between these definitions is established in `SSYTEquiv.lean` via
    `SSYTEquiv.ssytEquiv`. Use `SSYTEquiv.toSchurBasicsSSYT` and `SSYTEquiv.toSFSSYT`
    to convert between representations.

    **When to use which:**
    - Use this definition when working with cell coordinates `(i, j)` directly, or when
      extending the `YoungTableau` structure is beneficial.
    - Use `SymmetricFunctions.SSYT` when the dependent type ensures bounds checking at
      compile time, or when `[NeZero N]` is not available. -/
structure SSYT {N : ℕ} [NeZero N] (lam : NPartition N) extends YoungTableau lam where
  /-- Entries increase weakly along rows -/
  row_weak : ∀ i : Fin N, ∀ j₁ j₂ : ℕ, (i, j₂) ∈ lam.youngDiagram → j₁ < j₂ →
    entry (i, j₁) ≤ entry (i, j₂)
  /-- Entries increase strictly down columns -/
  col_strict : ∀ i₁ i₂ : Fin N, ∀ j : ℕ, (i₂, j) ∈ lam.youngDiagram → i₁ < i₂ →
    entry (i₁, j) < entry (i₂, j)

end
