/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Combinatorics.Young.LittlewoodRichardson.Part17
import Def.Combinatorics.Enumerative.Partition.NPartition.Part9
import Instance.GroupTheory.Perm.Basics.Part2
import Lemma.MvPolynomial.LittlewoodRichardson
import Instance.Combinatorics.Young.SchurBasics.Part7
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

/-! ### Bridge between SchurBasics and LittlewoodRichardson representations

The two files use different indexing conventions for skew diagrams:
- `SchurBasics.lean`: 0-indexed columns, `mu.parts i ≤ j < lam.parts i`
- `LittlewoodRichardson.lean`: 1-indexed columns, `mu i < j ≤ lam i`

The bijection between cells is: (i, j) ↔ (i, j+1)

We define equivalences to bridge these representations. -/


/-- Cell bijection: SchurBasics cell (i, j) ↔ LittlewoodRichardson cell (i, j+1).
    
    SchurBasics: (i, j) ∈ Y(λ/μ) iff μ_i ≤ j < λ_i
    LittlewoodRichardson: (i, j) ∈ Y(λ/μ) iff μ_i < j ≤ λ_i
    
    The map (i, j) ↦ (i, j+1) transforms the first to the second. -/
def skewCellEquiv {N : ℕ} [NeZero N] (lam mu : NPartition N) :
    { c // c ∈ skewYoungDiagram lam mu } ≃
    { c // c ∈ AlgebraicCombinatorics.skewYoungDiagram lam.parts mu.parts } where
  toFun := fun ⟨c, hc⟩ => ⟨(c.1, c.2 + 1), by
    rw [mem_skewYoungDiagram] at hc
    simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · show mu.parts c.1 < c.2 + 1; omega
    · show c.2 + 1 ≤ lam.parts c.1; omega⟩
  invFun := fun ⟨c, hc⟩ => ⟨(c.1, c.2 - 1), by
    simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq] at hc
    rw [mem_skewYoungDiagram]
    refine ⟨?_, ?_⟩
    · show mu.parts c.1 ≤ c.2 - 1; omega
    · show c.2 - 1 < lam.parts c.1; omega⟩
  left_inv := fun ⟨c, hc⟩ => by simp
  right_inv := fun ⟨c, hc⟩ => by
    simp only [AlgebraicCombinatorics.skewYoungDiagram, Set.mem_ofPred_eq] at hc
    ext
    · rfl
    · simp; omega

/-- Filling bijection: convert between SkewFilling and Tableau.
    
    This bridges the two representations by composing with the cell bijection. -/
def skewFillingEquiv {N : ℕ} [NeZero N] (lam mu : NPartition N) :
    SkewFilling lam mu ≃ AlgebraicCombinatorics.Tableau lam.parts mu.parts :=
  Equiv.arrowCongr (skewCellEquiv lam mu) (Equiv.refl _)

/-- The finite set of all valid SSYT fillings. -/
def ssytFillings {N : ℕ} [NeZero N] (lam mu : NPartition N) : Finset (SkewFilling lam mu) :=
  Finset.univ.filter (isSSYTFilling lam mu)

/-- The monomial associated to a filling.
    x_f = ∏_{c ∈ Y(λ/μ)} x_{f(c)} -/
def fillingMonomial {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (f : SkewFilling lam mu) : MvPolynomial (Fin N) ℤ :=
  ∏ c : { c // c ∈ skewYoungDiagram lam mu }, X (f c)

/-- The content of a filling: the number of cells with each entry value.
    content(f)(i) = |{c ∈ Y(λ/μ) : f(c) = i}|
    
    This is related to the monomial by: x_f = ∏_i x_i^{content(f)(i)}
    
    The Bender-Knuth involution BK_k swaps the content of k and k+1:
    content(BK_k(f))(k) = content(f)(k+1) and content(BK_k(f))(k+1) = content(f)(k) -/
def fillingContent {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (f : SkewFilling lam mu) : Fin N → ℕ :=
  fun i => Finset.univ.filter (fun c : { c // c ∈ skewYoungDiagram lam mu } => f c = i) |>.card

/-- The skew Schur polynomial s_{λ/μ} is the sum of monomials x_T over all
    semistandard skew tableaux of shape λ/μ.
    Definition \ref{def.sf.skew-schur} in the source.

    We define this as a sum over the finite set of valid SSYT fillings:
    s_{λ/μ} = ∑_{T ∈ SSYT(λ/μ)} x_T

    The definition proceeds by:
    1. Representing tableaux as functions from the skew diagram to Fin N
    2. Filtering for those satisfying the SSYT conditions (row-weak, column-strict)
    3. Summing the associated monomials

    ## Relationship to Other Definitions

    This project has two skew Schur polynomial definitions with different design tradeoffs:

    | Definition | File | Input | Ring | Use case |
    |------------|------|-------|------|----------|
    | `skewSchurPoly` (this) | SchurBasics.lean | `NPartition N` | `ℤ` | Proofs using skew diagrams, symmetry |
    | `AlgebraicCombinatorics.skewSchurPoly` | LittlewoodRichardson.lean | `Fin N → ℕ` | generic `R` | Littlewood-Richardson rule, generic rings |

    **When to use which:**
    - Use **this definition** when working with skew Young diagrams, SSYT fillings, or proving
      symmetry properties. It requires `[NeZero N]` and uses integer coefficients.
    - Use **`AlgebraicCombinatorics.skewSchurPoly`** when you need a generic coefficient ring
      or when working with the Littlewood-Richardson rule. It takes unbundled `Fin N → ℕ`.

    **Equivalence:** See `SSYTEquiv.lean` for the bridge between these definitions. -/
def skewSchurPoly {N : ℕ} [NeZero N] (lam mu : NPartition N) : MvPolynomial (Fin N) ℤ :=
  ∑ f ∈ ssytFillings lam mu, fillingMonomial f

/-- Applying a permutation σ to each entry of a filling. -/
def applyPermToFilling {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (σ : Equiv.Perm (Fin N)) (f : SkewFilling lam mu) : SkewFilling lam mu :=
  fun c => σ (f c)

/-! ## Bender-Knuth Involutions

The Bender-Knuth involution is a key tool for proving that Schur polynomials are symmetric.
For each k ∈ {0, 1, ..., N-2}, the Bender-Knuth involution BK_k is a bijection on the set
of semistandard Young tableaux that swaps certain entries k and k+1 while preserving
the semistandardness property.

### Key Properties

1. **Involution**: BK_k ∘ BK_k = id
2. **Preserves shape**: BK_k(T) has the same shape as T
3. **Monomial effect**: x_{BK_k(T)} = (swap x_k x_{k+1}) · x_T

### How BK_k Works

For each row i:
- Consider cells containing k or k+1
- Some cells are "forced" (must stay the same due to column constraints)
- The remaining "free" cells can be swapped
- BK_k swaps the free k's and (k+1)'s while maintaining semistandardness

A cell (i, j) with entry k is "forced" if there exists a cell (i', j) with i' > i
in the same column with entry k+1 (column-strict constraint would be violated).
Similarly for entry k+1 being forced by a k above it.

**Note:** The full implementation of the Bender-Knuth involution requires careful handling
of decidability instances. The proofs below are complete and sorry-free.
-/


/-- The simple transposition swapping k and k+1.
    
    This is an alternative signature for `AlgebraicCombinatorics.simpleTransposition`.
    Instead of taking `Fin (N - 1)` (which encodes the constraint), this takes
    `Fin N` with an explicit proof `hk : k.val + 1 < N`.
    
    See `simpleTransposition_eq_canonical` for the equivalence with the canonical definition. -/
def simpleTransposition {N : ℕ} (k : Fin N) (hk : k.val + 1 < N) : Equiv.Perm (Fin N) :=
  Equiv.swap k ⟨k.val + 1, hk⟩

/-- The Bender-Knuth involution BK_k on skew fillings.
    
    For a filling f and index k, BK_k swaps certain entries k and k+1 while preserving
    the semistandardness property. The construction works row by row:
    - In each row, identify which k's and (k+1)'s are "free" (not forced by column constraints)
    - Use parenthesis-matching: each free (k+1) "matches" with the nearest unmatched free k to its left
    - Only UNMATCHED free entries get swapped
    
    **Implementation**: This bridges to the full implementation in `LittlewoodRichardson.lean`
    via `skewFillingEquiv`. For SSYT fillings, it applies `AlgebraicCombinatorics.benderKnuth`;
    for non-SSYT fillings, it returns the input unchanged (the lemmas only apply to SSYT anyway). -/
def benderKnuthInvol {N : ℕ} [NeZero N] (lam mu : NPartition N) 
    (k : Fin N) (hk : k.val + 1 < N) (f : SkewFilling lam mu) : SkewFilling lam mu := by
  classical
  -- Convert to Tableau representation
  let T := skewFillingEquiv lam mu f
  -- Check if T is semistandard
  by_cases hT : AlgebraicCombinatorics.IsSemistandard T
  · -- Apply the real Bender-Knuth involution and convert back
    exact (skewFillingEquiv lam mu).symm (AlgebraicCombinatorics.benderKnuth k hk T hT)
  · -- For non-SSYT fillings, return unchanged
    exact f

end
