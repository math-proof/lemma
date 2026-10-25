/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
import Def.Combinatorics.Young.SchurBasics.Part7
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

/-- Membership in a skew Young diagram: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i.
    This is the 0-indexed version of the textbook condition μ_i < j ≤ λ_i. -/
theorem mem_skewYoungDiagram {N : ℕ} [NeZero N] {lam mu : NPartition N} {c : Fin N × ℕ} :
    c ∈ skewYoungDiagram lam mu ↔ mu.parts c.1 ≤ c.2 ∧ c.2 < lam.parts c.1 := by
  simp only [skewYoungDiagram, Finset.mem_sdiff, NPartition.mem_youngDiagram]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨Nat.not_lt.mp h2, h1⟩
  · intro ⟨h1, h2⟩
    exact ⟨h2, Nat.not_lt.mpr h1⟩

end
