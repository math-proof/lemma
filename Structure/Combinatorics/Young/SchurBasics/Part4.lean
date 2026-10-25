/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
import Def.Combinatorics.Young.SchurBasics.Part8
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

/-- A semistandard skew Young tableau is a skew tableau where:
    - entries increase weakly along each row (left to right)
    - entries increase strictly down each column (top to bottom)
    Definition \ref{def.sf.skew-ssyt} in the source.

    **Note:** This is one of two SkewSSYT definitions in this project:
    - **This definition** (`SchurBasics.SkewSSYT`): Uses `entry : Fin N × ℕ → Fin N` with a
      support condition. Extends `SkewYoungTableau`. Takes `lam mu : NPartition N` as separate
      arguments. Requires `[NeZero N]`. Field names: `row_weak`, `col_strict`.
    - **Alternative definition** (`SymmetricFunctions.SkewSSYT` in `PieriJacobiTrudi.lean`):
      Uses dependent types. Takes `s : SkewPartition N` as a single bundled argument.
      No `[NeZero N]` requirement. Field names: `rowWeak`, `colStrict`.

    See `SSYTEquiv.lean` for conversions between representations. -/
structure SkewSSYT {N : ℕ} [NeZero N] (lam mu : NPartition N) extends SkewYoungTableau lam mu where
  /-- Entries increase weakly along rows -/
  row_weak : ∀ i : Fin N, ∀ j₁ j₂ : ℕ,
    (i, j₁) ∈ skewYoungDiagram lam mu → (i, j₂) ∈ skewYoungDiagram lam mu → j₁ < j₂ →
    entry (i, j₁) ≤ entry (i, j₂)
  /-- Entries increase strictly down columns -/
  col_strict : ∀ i₁ i₂ : Fin N, ∀ j : ℕ,
    (i₁, j) ∈ skewYoungDiagram lam mu → (i₂, j) ∈ skewYoungDiagram lam mu → i₁ < i₂ →
    entry (i₁, j) < entry (i₂, j)

end
