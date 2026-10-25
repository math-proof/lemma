/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
import Instance.Combinatorics.Young.SchurBasics.Part2
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

/-! ## Monomials from tableaux -/


/-- The monomial x_T associated to a Young tableau T.
    Definition \ref{def.sf.ytab.xT} in the source.
    x_T = ∏_{c ∈ Y(lam)} x_{T(c)} -/
def YoungTableau.monomial {N : ℕ} [NeZero N] {lam : NPartition N}
    (T : YoungTableau lam) : MvPolynomial (Fin N) ℤ :=
  ∏ c ∈ lam.youngDiagram, X (T.entry c)

namespace YoungTableau

variable {N : ℕ} [NeZero N] {lam : NPartition N}

/-! ### API lemmas for YoungTableau.monomial (Definition def.sf.ytab.xT)

These lemmas provide the alternative characterization of x_T as a product of powers,
matching the third form of the definition:
  x_T = ∏_{k=1}^N x_k^{(# of times k appears in T)}
-/


/-- The number of times a value k appears in a Young tableau T.
    This is the count #{c ∈ Y(λ) | T(c) = k}. -/
def occurrences (T : YoungTableau lam) (k : Fin N) : ℕ :=
  (lam.youngDiagram.filter fun c => T.entry c = k).card

end YoungTableau

/-! ## Schur Polynomials -/
/-! ### Finiteness of SSYT

To define the Schur polynomial as a sum over all semistandard Young tableaux,
we need to show that the set of such tableaux is finite. The key insight is that:
1. The Young diagram Y(λ) is a finite set
2. Entries are bounded (they live in Fin N)
3. The SSYT conditions are decidable

We represent tableaux as functions from the diagram to Fin N, and filter for those
satisfying the SSYT conditions.
-/


/-- The type of all fillings of a Young diagram with entries in Fin N.
    This is finite since the diagram is finite and Fin N is finite. -/
def Filling {N : ℕ} [NeZero N] (lam : NPartition N) : Type :=
  { c // c ∈ lam.youngDiagram } → Fin N

end
