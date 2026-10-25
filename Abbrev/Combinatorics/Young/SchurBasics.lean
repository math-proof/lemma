/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
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

/-!
## N-Partitions

This file uses the canonical `NPartition` definition from
`AlgebraicCombinatorics/SymmetricFunctions/NPartition.lean`.

The canonical definition uses `antitone` as the field name, but provides
a `monotone` alias theorem for compatibility. The weakly decreasing
condition means: if `i ≤ j` then `parts j ≤ parts i`.
-/
/-! ## The ρ vector

Definition \ref{def.sf.alternants}(a) in the source defines the ρ vector as the N-tuple
(N-1, N-2, ..., 0). In Lean, we use 0-based indexing via `Fin N`, so:
- ρ(0) = N - 1
- ρ(1) = N - 2
- ...
- ρ(N-1) = 0

For example, when N = 3, we have ρ = (2, 1, 0).
-/


/-- The ρ vector is the N-tuple (N-1, N-2, ..., 0).
    Definition \ref{def.sf.alternants}(a) in the source.

    Note: The textbook uses 1-based indexing with ρ_j = N - j for j ∈ [N].
    In Lean with 0-based indexing, this becomes ρ(i) = N - 1 - i for i ∈ Fin N.

    This is an abbreviation for `AlgebraicCombinatorics.rho N` from LittlewoodRichardson.lean. -/
abbrev rhoVector (N : ℕ) : Fin N → ℕ := AlgebraicCombinatorics.rho N

end
