/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import sympy.combinatorics.symmetric.LittlewoodRichardson
import sympy.combinatorics.partitions.NPartition
import sympy.combinatorics.permutations.Basics
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

omit [NeZero N] in
/-- The ρ vector is weakly decreasing -/
theorem rhoVector_antitone : Antitone (rhoVector N) :=
  AlgebraicCombinatorics.rho_antitone

/-- The ρ vector as an N-partition (when N > 0) -/
def rhoPartition (N : ℕ) [NeZero N] : NPartition N where
  parts := rhoVector N
  antitone := rhoVector_antitone N
/-! ## Alternants

Definition \ref{def.sf.alternants}(b) in the source defines the alternant a_α for an
N-tuple α = (α_1, α_2, ..., α_N) as the determinant:

  a_α = det((x_i^{α_j})_{1≤i≤N, 1≤j≤N})

where entry (i, j) is x_i^{α_j}. This is a polynomial in R[x_1, ..., x_N].

In our implementation, we use:
  alternant N α = det(Matrix.of (fun i j => X j ^ α i))

This gives entry (i, j) = x_j^{α_i}, which is the transpose of the textbook matrix.
Since det(A) = det(A^T), both definitions yield the same polynomial.

For example, when N = 3 and α = (5, 3, 0), the textbook matrix is:
  | x_1^5  x_1^3  x_1^0 |
  | x_2^5  x_2^3  x_2^0 |
  | x_3^5  x_3^3  x_3^0 |

and our matrix is the transpose of this.
-/


variable {R : Type*} [CommRing R]

/-- The alternant a_α for an N-tuple α.
    Definition \ref{def.sf.alternants}(b) in the source.

    This is an abbreviation for `AlgebraicCombinatorics.alternant` from LittlewoodRichardson.lean,
    which defines it as ∑_{σ ∈ S_N} sign(σ) · x^(σ·α). This equals the determinant-based
    definition det(x_j^{α_i}) by `AlgebraicCombinatorics.alternant_eq_det`.

    The explicit `N` parameter is kept for backward compatibility with existing code. -/
noncomputable abbrev alternant (N : ℕ) (α : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  AlgebraicCombinatorics.alternant α

/-- Alternative definition matching the textbook convention exactly:
    entry (i, j) = x_i^{α_j}. This equals `alternant` since det(A) = det(A^T). -/
def alternantTextbook (N : ℕ) (α : Fin N → ℕ) : MvPolynomial (Fin N) R :=
  Matrix.det (Matrix.of fun i j => (X i : MvPolynomial (Fin N) R) ^ α j)
/-! ## Young Diagrams for N-partitions

The Young diagram infrastructure is now provided by `NPartition.lean`.
See `NPartition.youngDiagram`, `NPartition.mem_youngDiagram`, etc.
-/
/-! ## Young Tableaux -/


/-- A Young tableau of shape lam is a filling of the Young diagram Y(lam) with elements of [N].
    Definition \ref{def.sf.ytab} in the source. -/
structure YoungTableau {N : ℕ} [NeZero N] (lam : NPartition N) where
  /-- The filling function -/
  entry : Fin N × ℕ → Fin N
  /-- The entry is only meaningful for cells in the diagram -/
  support : ∀ c, c ∉ lam.youngDiagram → entry c = 0

namespace YoungTableau

variable {N : ℕ} [NeZero N] {lam : NPartition N}

/-- Two Young tableaux are equal iff their entries agree. -/
@[ext]
theorem ext {T₁ T₂ : YoungTableau lam} (h : ∀ c, T₁.entry c = T₂.entry c) : T₁ = T₂ := by
  cases T₁; cases T₂
  simp only [mk.injEq]
  funext c
  exact h c

/-- Coercion to function, allowing T c notation. -/
instance : CoeFun (YoungTableau lam) (fun _ => Fin N × ℕ → Fin N) := ⟨entry⟩

/-- Entry at row i, column j. -/
def entryAt (T : YoungTableau lam) (i : Fin N) (j : ℕ) : Fin N := T.entry (i, j)

/-- The number of cells in the tableau (equals the size of the Young diagram). -/
def size (_T : YoungTableau lam) : ℕ := lam.youngDiagram.card

end YoungTableau

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

namespace SSYT

variable {N : ℕ} [NeZero N] {lam : NPartition N}
/-! ### Basic Properties -/


/-- Two SSYTs are equal iff their entries agree on all cells. -/
@[ext]
theorem ext {T₁ T₂ : SSYT lam} (h : ∀ c, T₁.entry c = T₂.entry c) : T₁ = T₂ := by
  cases T₁; cases T₂
  simp only [mk.injEq]
  exact YoungTableau.ext h
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

/-- The highest weight tableau exists for any partition. -/
instance (lam : NPartition N) : Inhabited (SSYT lam) := ⟨highestWeight lam⟩

end SSYT
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

/-- Fillings are finite. -/
noncomputable instance filling_fintype {N : ℕ} [NeZero N] (lam : NPartition N) :
    Fintype (Filling lam) :=
  @Fintype.ofFinite _ Pi.finite

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

/-- The SSYT condition is decidable since we're quantifying over finite types. -/
instance isSSYTFillingYoung_decidable {N : ℕ} [NeZero N] (lam : NPartition N)
    (f : Filling lam) : Decidable (isSSYTFillingYoung lam f) := by
  unfold isSSYTFillingYoung
  infer_instance

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
/-! ## Skew Young Tableaux -/


/-- A skew Young tableau of shape λ/μ is a filling of Y(λ/μ) with elements of [N].
    Definition \ref{def.sf.skew-tab} in the source.

    Formally, a Young tableau of shape λ/μ is a map T : Y(λ/μ) → [N].
    We represent this as a total function `entry : Fin N × ℕ → Fin N` with a support
    condition that entries outside the skew diagram are 0.

    Young tableaux of shape λ/μ are often called "skew Young tableaux".

    Note: If μ ⊈ λ (i.e., not μ ≤ λ), then there are no Young tableaux of shape λ/μ
    because the skew diagram would be empty or malformed. -/
structure SkewYoungTableau {N : ℕ} [NeZero N] (lam mu : NPartition N) where
  /-- The filling function T : Y(λ/μ) → [N] -/
  entry : Fin N × ℕ → Fin N
  /-- The entry is only meaningful for cells in the skew diagram -/
  support : ∀ c, c ∉ skewYoungDiagram lam mu → entry c = 0

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

/-- Coercion to function -/
instance : CoeFun (SkewYoungTableau lam mu) (fun _ => Fin N × ℕ → Fin N) := ⟨entry⟩

/-- The empty skew tableau when lam = mu -/
def empty (lam : NPartition N) : SkewYoungTableau lam lam where
  entry := fun _ => 0
  support := fun _ _ => rfl

/-- The number of cells in a skew Young tableau -/
def size (_T : SkewYoungTableau lam mu) : ℕ :=
  (skewYoungDiagram lam mu).card

/-- Entry at a specific row and column -/
def entryAt (T : SkewYoungTableau lam mu) (i : Fin N) (j : ℕ) : Fin N :=
  T.entry (i, j)

/-- A skew tableau is nonempty if the skew diagram is nonempty -/
def Nonempty (_T : SkewYoungTableau lam mu) : Prop :=
  (skewYoungDiagram lam mu).Nonempty

end SkewYoungTableau

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
/-! ## Properties of Semistandard Skew Tableaux -/
/-! ## Monomials from Skew Tableaux -/


/-- The monomial x_T associated to a skew Young tableau T.
    Definition \ref{def.sf.ytab.skew-xT} in the source.
    x_T = ∏_{c ∈ Y(lam/mu)} x_{T(c)} -/
def SkewYoungTableau.monomial {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (T : SkewYoungTableau lam mu) : MvPolynomial (Fin N) ℤ :=
  ∏ c ∈ skewYoungDiagram lam mu, X (T.entry c)

namespace SkewYoungTableau

variable {N : ℕ} [NeZero N] {lam mu : NPartition N}

/-- The number of times a value k appears in a skew tableau T.
    This is the exponent of x_k in the monomial x_T. -/
def countValue (T : SkewYoungTableau lam mu) (k : Fin N) : ℕ :=
  (skewYoungDiagram lam mu).filter (fun c => T.entry c = k) |>.card

/-- For a semistandard skew tableau, the monomial is the same. -/
def SkewSSYT.monomial' {N : ℕ} [NeZero N] {lam mu : NPartition N}
    (T : SkewSSYT lam mu) : MvPolynomial (Fin N) ℤ :=
  T.toSkewYoungTableau.monomial

end SkewYoungTableau
/-! ## Skew Schur Polynomials -/
/-! ### Finiteness of SkewSSYT

To define the skew Schur polynomial as a sum over all semistandard skew tableaux,
we need to show that the set of such tableaux is finite. The key insight is that:
1. The skew diagram Y(λ/μ) is a finite set
2. Entries are bounded (they live in Fin N)
3. The SSYT conditions are decidable

We represent tableaux as functions from the diagram to Fin N, and filter for those
satisfying the SSYT conditions.
-/


/-- The type of all fillings of a skew diagram with entries in Fin N.
    This is finite since the diagram is finite and Fin N is finite. -/
def SkewFilling {N : ℕ} [NeZero N] (lam mu : NPartition N) : Type :=
  { c // c ∈ skewYoungDiagram lam mu } → Fin N

/-- Fillings are finite. -/
noncomputable instance skewFilling_fintype {N : ℕ} [NeZero N] (lam mu : NPartition N) :
    Fintype (SkewFilling lam mu) :=
  @Fintype.ofFinite _ Pi.finite

/-- The set of fillings that correspond to valid semistandard tableaux.
    We check the conditions on pairs of cells in the diagram:
    - Row-weak: if c1 and c2 are in the same row with c1 to the left, then f(c1) ≤ f(c2)
    - Column-strict: if c1 and c2 are in the same column with c1 above, then f(c1) < f(c2) -/
def isSSYTFilling {N : ℕ} [NeZero N] (lam mu : NPartition N) (f : SkewFilling lam mu) : Prop :=
  -- Row-weak condition: check all pairs in the same row
  (∀ c1 c2 : { c // c ∈ skewYoungDiagram lam mu },
    c1.val.1 = c2.val.1 → c1.val.2 < c2.val.2 → f c1 ≤ f c2) ∧
  -- Column-strict condition: check all pairs in the same column
  (∀ c1 c2 : { c // c ∈ skewYoungDiagram lam mu },
    c1.val.2 = c2.val.2 → c1.val.1 < c2.val.1 → f c1 < f c2)

/-- The SSYT condition is decidable since we're quantifying over finite types. -/
instance isSSYTFilling_decidable {N : ℕ} [NeZero N] (lam mu : NPartition N)
    (f : SkewFilling lam mu) : Decidable (isSSYTFilling lam mu f) := by
  unfold isSSYTFilling
  infer_instance
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
/-! ## Schur Polynomials are Symmetric -/
/-! ## Properties of Alternants -/
