/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Instance.LinearAlgebra.Matrix.Determinant.CauchyBinet
set_option backward.isDefEq.respectTransparency false
open scoped Matrix BigOperators
open Finset Matrix

/-!
# Determinants: Cauchy-Binet and Related Formulas

This file formalizes the Cauchy-Binet formula and related determinant identities,
following Section "Cauchy--Binet ... Factoring the matrix" of the source
(CauchyBinet.tex).

## Main definitions

* `Matrix.submatrix` - The submatrix obtained by restricting to specific rows and columns.
  This corresponds to `sub_U^V A` in the source (Definition def.det.sub).
* `colsSubmatrix`, `rowsSubmatrix` - Submatrices selecting specific columns/rows.

## Main results

* `cauchyBinet` - The general Cauchy-Binet formula for det(AB) where A is n×m and B is m×n
  (Theorem thm.det.CB)
* `cauchyBinet_square` - Special case for square matrices: det(AB) = det(A)·det(B)
* `det_mul_eq_zero_of_rank_deficient` - When m < n, det(AB) = 0
* `det_add_sum` - Formula for det(A+B) as a double sum over subsets (Theorem thm.det.det(A+B))
* `det_diagonal_submatrix_eq`, `det_diagonal_submatrix_off_diag` - Minors of diagonal matrices
  (Lemma lem.det.minors-diag)
* `det_add_diagonal` - Simplified formula when adding a diagonal matrix (Theorem thm.det.det(A+D))
* `det_const_add_diagonal` - Determinant of x + D where D is diagonal (Proposition prop.det.x+ai)
* `det_charPoly_coeff` - Coefficients of the characteristic polynomial
  (Proposition prop.det.charpol-explicit)
* `det_pascal_matrix` - The Pascal matrix has determinant 1 (Proposition prop.det.pascal-LU)

## References

* Source: CauchyBinet.tex

## Implementation notes

Mathlib already provides `Matrix.det_mul` in `Mathlib.LinearAlgebra.Matrix.Determinant`.
We provide additional results and connect Mathlib's API to the textbook presentation.

The submatrix operation `Matrix.submatrix` uses functions for row/column selection,
which is more general than the textbook's subset-based notation.
-/


namespace AlgebraicCombinatorics

namespace CauchyBinet

variable {R : Type*} [CommRing R]

/-- A permutation "preserves [k]" if it maps elements with index < k to elements with index < k. -/
def preservesPrefix {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ) : Prop :=
  ∀ i : Fin n, i.val < k ↔ (σ i).val < k

/-- Restriction of a permutation to {i | i.val < k} using Mathlib's `subtypePerm`. -/
noncomputable def restrictToLt {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (hσ : preservesPrefix σ k) : Equiv.Perm {i : Fin n // ltPred n k i} :=
  σ.subtypePerm fun i => by
    simp only [ltPred]
    exact (hσ i).symm

/-- Restriction of a permutation to {i | i.val ≥ k} using Mathlib's `subtypePerm`. -/
noncomputable def restrictToGe {n : ℕ} (σ : Equiv.Perm (Fin n)) (k : ℕ)
    (hσ : preservesPrefix σ k) : Equiv.Perm {i : Fin n // ¬ltPred n k i} :=
  σ.subtypePerm fun i => by
    simp only [ltPred, not_lt]
    constructor
    · intro h
      exact Nat.le_of_not_lt fun hc => Nat.not_lt.mpr h ((hσ i).mp hc)
    · intro h
      exact Nat.le_of_not_lt fun hc => Nat.not_lt.mpr h ((hσ i).mpr hc)

/-- The finset {0, 1, ..., k-1} ⊆ Fin n. -/
def prefixFinset (n k : ℕ) (_hk : k ≤ n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val < k)

/-- Equivalence between Fin k and the subtype {i : Fin n // i.val < k}. -/
noncomputable def finEquivSubtypeLt (n k : ℕ) (hk : k ≤ n) : 
    Fin k ≃ {i : Fin n // ltPred n k i} := by
  refine ⟨fun j => ⟨⟨j.val, by omega⟩, j.isLt⟩, 
         fun x => ⟨x.val.val, x.prop⟩, ?_, ?_⟩
  · intro j; rfl
  · intro x; rfl

/-- Equivalence between Fin (n-k) and the subtype {i : Fin n // ¬(i.val < k)}. -/
noncomputable def finEquivSubtypeGe (n k : ℕ) (hk : k ≤ n) : 
    Fin (n - k) ≃ {i : Fin n // ¬ltPred n k i} := by
  refine ⟨fun j => ⟨⟨j.val + k, ?_⟩, ?_⟩, 
         fun x => ⟨x.val.val - k, ?_⟩, ?_, ?_⟩
  · have hj := j.isLt; omega
  · have hj := j.isLt; simp only [ltPred, not_lt]; omega
  · have hx := x.prop
    have hxlt := x.val.isLt
    simp only [ltPred] at hx
    push Not at hx
    omega
  · intro j
    simp only [Fin.ext_iff]
    have hj := j.isLt
    have : j.val + k - k = j.val := Nat.add_sub_cancel j.val k
    exact this
  · intro x
    simp only [Subtype.ext_iff, Fin.ext_iff]
    have hx := x.prop
    simp only [ltPred] at hx
    push Not at hx
    have : x.val.val - k + k = x.val.val := Nat.sub_add_cancel hx
    exact this

/-- Convert restrictToLt to a permutation on Fin k using finEquivSubtypeLt. -/
noncomputable def restrictToLtAsFink {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin n)) 
    (hσ : preservesPrefix σ k) : Equiv.Perm (Fin k) :=
  (finEquivSubtypeLt n k hk).symm.permCongr (restrictToLt σ k hσ)

/-- Convert restrictToGe to a permutation on Fin (n-k) using finEquivSubtypeGe. -/
noncomputable def restrictToGeAsFinNK {n k : ℕ} (hk : k ≤ n) (σ : Equiv.Perm (Fin n)) 
    (hσ : preservesPrefix σ k) : Equiv.Perm (Fin (n - k)) :=
  (finEquivSubtypeGe n k hk).symm.permCongr (restrictToGe σ k hσ)

/-!
## Minors of Diagonal Matrices (Lemma lem.det.minors-diag)

For a diagonal matrix D with entries d₁, d₂, ..., dₙ:

(a) det(sub_P^P D) = ∏_{i ∈ P} dᵢ  (principal minors are products of diagonal entries)
(b) If P ≠ Q with |P| = |Q|, then det(sub_P^Q D) = 0  (off-diagonal submatrices have zero det)
-/
/-!
## Determinant of A + D (Theorem thm.det.det(A+D))

When B = D is diagonal with entries d₁, ..., dₙ, the formula for det(A+B) simplifies:
  det(A+D) = ∑_{P ⊆ [n]} det(sub_P^P A) · ∏_{i ∈ [n]\P} dᵢ

The cross terms vanish because det(sub_P̃^Q̃ D) = 0 when P ≠ Q.
-/
/-!
## Determinant of x + D (Proposition prop.det.x+ai)

For the matrix F with entries F_{i,j} = x + d_i [i=j], i.e.,
  F = (x x ... x)
      (x x+d₂ ... x)
      (⋮  ⋮  ⋱  ⋮)
      (x x ... x+dₙ)

we have:
  det F = d₁d₂...dₙ + x ∑_{i=1}^n d₁d₂...d̂ᵢ...dₙ

where d̂ᵢ means "omit dᵢ".

This is useful in graph theory (e.g., Laplacian matrices).
-/


/-- The matrix with x on all entries except diagonal which has x + dᵢ.
    (Used in Proposition prop.det.x+ai) -/
def constPlusDiagMatrix {n : ℕ} (x : R) (d : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => x + if i = j then d i else 0

/-- The set of fixed points of a permutation. -/
def fixedPoints' {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => σ i = i)

/-- The constant x matrix (all entries equal to x). -/
def constMatrix {n : ℕ} (x : R) : Matrix (Fin n) (Fin n) R :=
  fun _ _ => x

/-!
## Characteristic Polynomial Coefficients (Proposition prop.det.charpol-explicit)

The characteristic polynomial of A is det(xI - A) (or det(A + xI) up to sign).
Its coefficients are sums of principal minors:

  det(A + xI) = ∑_{k=0}^n (∑_{P ⊆ [n], |P|=n-k} det(sub_P^P A)) · x^k

The coefficient of x^{n-k} is the sum of all k×k principal minors of A.
-/
/-!
## Pascal Matrix Determinant (Proposition prop.det.pascal-LU)

The Pascal matrix P_n has entries P_{i,j} = C(i+j-2, i-1), i.e.,
  P = (C(0,0) C(1,0) ... C(n-1,0))
      (C(1,1) C(2,1) ... C(n,1))
      (⋮      ⋮      ⋱   ⋮)
      (C(n-1,n-1) C(n,n-1) ... C(2n-2,n-1))

For n=4, this is:
  (1 1 1 1)
  (1 2 3 4)
  (1 3 6 10)
  (1 4 10 20)

The determinant is 1, which can be proven via LU decomposition.
-/

/-- The Pascal matrix with entries C(i+j, i).
    (Proposition prop.det.pascal-LU)

    Note: We use 0-indexing, so entry (i,j) is C(i+j, i). -/
def pascalMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => (i.val + j.val).choose i.val

/-- The lower triangular factor L in the LU decomposition of the Pascal matrix.
    L_{i,k} = C(i, k) -/
def pascalLowerTriangular (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i k => i.val.choose k.val

/-- The upper triangular factor U in the LU decomposition of the Pascal matrix.
    U_{k,j} = C(j, k) -/
def pascalUpperTriangular (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun k j => j.val.choose k.val

/-!
## Additional Lemmas

Some auxiliary results used in the main theorems.
-/

end CauchyBinet
end AlgebraicCombinatorics
