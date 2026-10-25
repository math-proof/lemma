/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
import Instance.Combinatorics.Young.SchurBasics.Part3
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

/-- The set of fillings that correspond to valid semistandard tableaux.
    We check the conditions on pairs of cells in the diagram:
    - Row-weak: if c1 and c2 are in the same row with c1 to the left, then f(c1) ≤ f(c2)
    - Column-strict: if c1 and c2 are in the same column with c1 above, then f(c1) < f(c2) -/
def isSSYTFillingYoung {N : ℕ} [NeZero N] (lam : NPartition N) (f : Filling lam) : Prop :=
  -- Row-weak condition: check all pairs in the same row
  (∀ c1 c2 : { c // c ∈ lam.youngDiagram },
    c1.val.1 = c2.val.1 → c1.val.2 < c2.val.2 → f c1 ≤ f c2) ∧
  -- Column-strict condition: check all pairs in the same column
  (∀ c1 c2 : { c // c ∈ lam.youngDiagram },
    c1.val.2 = c2.val.2 → c1.val.1 < c2.val.1 → f c1 < f c2)

end
