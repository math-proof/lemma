/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
import Structure.Combinatorics.Young.SchurBasics.Part3
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

namespace SkewYoungTableau

variable {N : ℕ} [NeZero N] {lam mu : NPartition N}

/-- Two skew Young tableaux are equal if their entries agree on the skew diagram -/
@[ext]
theorem ext {T₁ T₂ : SkewYoungTableau lam mu}
    (h : ∀ c ∈ skewYoungDiagram lam mu, T₁.entry c = T₂.entry c) : T₁ = T₂ := by
  cases T₁ with | mk e₁ s₁ => ?_
  cases T₂ with | mk e₂ s₂ => ?_
  simp only [mk.injEq]
  funext c
  by_cases hc : c ∈ skewYoungDiagram lam mu
  · exact h c hc
  · rw [s₁ c hc, s₂ c hc]

end SkewYoungTableau
end
