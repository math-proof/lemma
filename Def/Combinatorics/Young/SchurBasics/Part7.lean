/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
import Instance.Combinatorics.Young.SchurBasics.Part4
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

/-- The finite set of all valid SSYT fillings of a Young diagram. -/
def ssytFillingsYoung {N : ℕ} [NeZero N] (lam : NPartition N) : Finset (Filling lam) :=
  Finset.univ.filter (isSSYTFillingYoung lam)

/-- The monomial associated to a filling of a Young diagram.
    x_f = ∏_{c ∈ Y(λ)} x_{f(c)} -/
def fillingMonomialYoung {N : ℕ} [NeZero N] {lam : NPartition N}
    (f : Filling lam) : MvPolynomial (Fin N) ℤ :=
  ∏ c : { c // c ∈ lam.youngDiagram }, X (f c)

/-- The Schur polynomial s_λ is the sum of monomials x_T over all SSYT of shape λ.
    Definition \ref{def.sf.schur} in the source.

    We define this as a sum over the finite set of valid SSYT fillings:
    s_λ = ∑_{T ∈ SSYT(λ)} x_T

    The definition proceeds by:
    1. Representing tableaux as functions from the Young diagram to Fin N
    2. Filtering for those satisfying the SSYT conditions (row-weak, column-strict)
    3. Summing the associated monomials

    This is equivalent to `skewSchurPoly lam 0` since `skewYoungDiagram lam 0 = lam.youngDiagram`.

    ## Relationship to Other Definitions

    This project has two Schur polynomial definitions with different design tradeoffs:

    | Definition | File | Input | Ring | Use case |
    |------------|------|-------|------|----------|
    | `schurPoly` (this) | SchurBasics.lean | `NPartition N` | `ℤ` | Proofs using Young diagrams, symmetry |
    | `AlgebraicCombinatorics.schurPoly` | LittlewoodRichardson.lean | `Fin N → ℕ` | generic `R` | Littlewood-Richardson rule, generic rings |

    **When to use which:**
    - Use **this definition** when working with Young diagrams, SSYT fillings, or proving
      symmetry properties. It requires `[NeZero N]` and uses integer coefficients.
    - Use **`AlgebraicCombinatorics.schurPoly`** when you need a generic coefficient ring
      or when working with the Littlewood-Richardson rule. It takes unbundled `Fin N → ℕ`.

    **Equivalence:** The two definitions agree when the partition is valid. See:
    - `SSYTEquiv.schurPoly_eq_schur`: relates this definition to `SymmetricFunctions.schur`
    - `schurPoly_eq_AC_schurPoly`: relates this definition to `AlgebraicCombinatorics.schurPoly` -/
def schurPoly {N : ℕ} [NeZero N] (lam : NPartition N) : MvPolynomial (Fin N) ℤ :=
  ∑ f ∈ ssytFillingsYoung lam, fillingMonomialYoung f

/-! ## Examples of Schur Polynomials -/

/-- Equivalence between cells in a column partition's Young diagram and Fin n.
    For a column partition (1,1,...,1,0,...,0) with n ones, the Young diagram
    consists of n cells in column 0, which can be identified with Fin n. -/
def col_partition_equiv {N : ℕ} [NeZero N] (n : ℕ) (hn : n ≤ N) (lam : NPartition N)
    (hlam : (∀ i : Fin N, i.val < n → lam.parts i = 1) ∧
            (∀ i : Fin N, i.val ≥ n → lam.parts i = 0)) :
    { c // c ∈ lam.youngDiagram } ≃ Fin n where
  toFun := fun ⟨c, hc⟩ => ⟨c.1.val, by
    rw [NPartition.mem_youngDiagram] at hc
    by_contra h; push Not at h
    have := hlam.2 c.1 h; rw [this] at hc
    exact Nat.not_lt_zero _ hc⟩
  invFun := fun ⟨k, hk⟩ => ⟨(⟨k, Nat.lt_of_lt_of_le hk hn⟩, 0), by
    rw [NPartition.mem_youngDiagram, hlam.1 ⟨k, Nat.lt_of_lt_of_le hk hn⟩ hk]
    exact Nat.zero_lt_one⟩
  left_inv := fun ⟨c, hc⟩ => by
    simp only [Subtype.mk.injEq]
    rw [NPartition.mem_youngDiagram] at hc
    by_cases hi : c.1.val < n
    · have hpart : lam.parts c.1 = 1 := hlam.1 c.1 hi
      rw [hpart] at hc; have hj : c.2 = 0 := by omega
      ext <;> simp [hj]
    · have hpart : lam.parts c.1 = 0 := hlam.2 c.1 (Nat.not_lt.mp hi)
      rw [hpart] at hc; exact absurd hc (Nat.not_lt_zero _)
  right_inv := fun ⟨k, hk⟩ => by simp

/-! ### Helper lemmas for schurPoly_21_eq -/
/-! ## Partition Containment

The partition containment infrastructure (LE, Preorder, PartialOrder, size, etc.)
is now provided by `NPartition.lean`. See `NPartition.instLE`, `NPartition.size`, etc.
-/
/-! ## Skew Young Diagrams

**Note**: The canonical `Finset` version of skew Young diagrams is `NPartition.skewYoungDiagram`
in `NPartition.lean`, which does not require `[NeZero N]`. The definition below is retained
for backwards compatibility but prefer `NPartition.skewYoungDiagram` for new code.

See also `AlgebraicCombinatorics.skewYoungDiagram` in LittlewoodRichardson.lean for the
`Set` version with 1-indexed columns (textbook convention).
-/


/-- The skew Young diagram Y(λ/μ) is the set difference Y(λ) \ Y(μ).
    Definition \ref{def.sf.skew-diag} in the source.

    **Note**: This is a duplicate of `NPartition.skewYoungDiagram` that requires `[NeZero N]`.
    Prefer `NPartition.skewYoungDiagram` for new code as it works for all `N`.

    For N-partitions λ and μ with μ ⊆ λ, the skew Young diagram Y(λ/μ) is defined as:
    ```
    Y(λ) \ Y(μ) = {(i,j) | i ∈ [N] and j ∈ [λ_i] \ [μ_i]}
                = {(i,j) | i ∈ [N] and j ∈ ℤ and μ_i < j ≤ λ_i}
    ```
    (The second form uses 1-indexed j as in the textbook.)

    In our 0-indexed formalization, this becomes:
    ```
    Y(λ/μ) = {(i,j) | i ∈ Fin N and μ_i ≤ j < λ_i}
    ```

    Example: Y((4,3,1)/(2,1,0)) consists of cells:
    - Row 0: (0, 2), (0, 3)  (since μ₀ = 2, λ₀ = 4)
    - Row 1: (1, 1), (1, 2)  (since μ₁ = 1, λ₁ = 3)
    - Row 2: (2, 0)          (since μ₂ = 0, λ₂ = 1) -/
def skewYoungDiagram {N : ℕ} [NeZero N] (lam mu : NPartition N) : Finset (Fin N × ℕ) :=
  lam.youngDiagram \ mu.youngDiagram

end
