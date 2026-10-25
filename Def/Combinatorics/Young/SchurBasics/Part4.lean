/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
import Theorem.Combinatorics.Young.SchurBasics.Part3
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

namespace SSYT

variable {N : ℕ} [NeZero N] {lam : NPartition N}

/-! ### Entry Bounds -/
/-! ### The Highest Weight Tableau -/


/-- The "highest weight" SSYT has entry i in every cell of row i.
    This is the semistandard tableau where each entry is the smallest possible value
    that an entry could have in that position (the row index).

    For example, for the partition (4, 2, 1), the highest weight tableau is:
    ```
    0 0 0 0
    1 1
    2
    ```
    where each row i is filled with the value i. -/
def highestWeight (lam : NPartition N) : SSYT lam where
  entry := fun c => if (c.1, c.2) ∈ lam.youngDiagram then c.1 else 0
  support := fun c hc => by simp [hc]
  row_weak := fun i j₁ j₂ h _ => by
    have h1 : (i, j₁) ∈ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram] at h ⊢
      exact Nat.lt_of_lt_of_le (Nat.lt_of_succ_le (Nat.succ_le_of_lt ‹j₁ < j₂›)) (Nat.le_of_lt h)
    simp [h, h1]
  col_strict := fun i₁ i₂ j h hi => by
    have h1 : (i₁, j) ∈ lam.youngDiagram := by
      rw [NPartition.mem_youngDiagram] at h ⊢
      calc j < lam.parts i₂ := h
        _ ≤ lam.parts i₁ := lam.monotone i₁ i₂ (le_of_lt hi)
    simp [h, h1, hi]

end SSYT
end
