/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Data.Fin.SkipTwo
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Lemma.Finset.PermFinset
open Matrix BigOperators Finset

/-!
# Determinants: Factor Hunting and Desnanot-Jacobi Identity

This file formalizes results from the "Factor hunting" and "Desnanot-Jacobi and Dodgson
condensation" sections of the determinants chapter.

## Main definitions

* `vandermondeMat`: The Vandermonde matrix with entries `a i ^ (n - j)`
* `cauchyMat`: The Cauchy matrix with entries `1 / (x i + y j)`

## Main results

### Vandermonde determinant (Theorem thm.det.vander)
* `vandermonde_det_a`: det(aᵢⁿ⁻ʲ) = ∏_{i<j} (aᵢ - aⱼ)
* `vandermonde_det_b`: det(aⱼⁿ⁻ⁱ) = ∏_{i<j} (aᵢ - aⱼ)
* `vandermonde_det_c`: det(aᵢʲ⁻¹) = ∏_{j<i} (aᵢ - aⱼ)
* `vandermonde_det_d`: det(aⱼⁱ⁻¹) = ∏_{j<i} (aᵢ - aⱼ)

### Proposition prop.det.(xi+yj)n-1
* `det_sum_pow`: det((xᵢ + yⱼ)ⁿ⁻¹) = (∏ₖ C(n-1,k)) · (∏_{i<j}(xᵢ-xⱼ)) · (∏_{i<j}(yⱼ-yᵢ))

### Laplace expansion (Theorem thm.det.laplace)
* `det_laplace_row`: det A = ∑_q (-1)^(p+q) A_{p,q} det(A_{~p,~q})
* `det_laplace_col`: det A = ∑_p (-1)^(p+q) A_{p,q} det(A_{~p,~q})

### Proposition prop.det.laplace.0
* `det_laplace_row_zero`: 0 = ∑_q (-1)^(p+q) A_{r,q} det(A_{~p,~q}) when p ≠ r
* `det_laplace_col_zero`: 0 = ∑_p (-1)^(p+q) A_{p,r} det(A_{~p,~q}) when q ≠ r

### Adjugate matrix (Definition def.det.adj, Theorem thm.det.adj.inverse)
* `adjugate`: The adjugate (classical adjoint) of a matrix
* `adjugate_mul`: A · adj(A) = det(A) · I
* `mul_adjugate`: adj(A) · A = det(A) · I

### Desnanot-Jacobi identity (Theorem thm.det.des-jac-1, thm.det.des-jac-2)
* `desnanot_jacobi`: det(A) · det(A') = det(A_{~1,~1}) · det(A_{~n,~n}) - det(A_{~1,~n}) · det(A_{~n,~1})
* `desnanot_jacobi_general`: Generalization with arbitrary rows p,q and columns u,v

### Cauchy determinant (Theorem thm.det.cauchy)
* `cauchy_det`: det(1/(xᵢ+yⱼ)) = ∏_{i<j}((xᵢ-xⱼ)(yᵢ-yⱼ)) / ∏_{i,j}(xᵢ+yⱼ)

### Jacobi's complementary minor theorem (Theorem thm.det.jacobi-complement)
* `jacobi_complementary_minor`: det(sub_P^Q(adj A)) = (-1)^(sum P + sum Q) · (det A)^(|Q|-1) · det(sub_{~Q}^{~P} A)

## References

* Source: DesnanotJacobi.tex (Factor hunting and Desnanot-Jacobi sections)

## Implementation notes

Many of these results are already in Mathlib under `Matrix.det_vandermonde`, `Matrix.adjugate`,
`Matrix.det_laplace_row`, etc. This file provides the statements matching the textbook
presentation and connects them to Mathlib's API.
-/


/-!
## Fin.succAbove computation lemmas

These simp lemmas allow efficient computation of `Fin.succAbove` for concrete Fin types.
They are used throughout this file for determinant expansions involving submatrices.
All lemmas are proved by `rfl` for maximum efficiency.
-/


/-!
## Fin 3 product lemmas

These lemmas simplify products over pairs and singletons in `Fin 3`.
They are used in Cauchy determinant computations for the n = 3 case.
-/


namespace AlgebraicCombinatorics

namespace Determinants

variable {R : Type*} [CommRing R]

variable {n : ℕ}

section SuccAboveLemmas

end SuccAboveLemmas

section Fin3ProductLemmas

variable {R : Type*} [CommMonoid R]

end Fin3ProductLemmas

/-!
## Vandermonde Determinant (Theorem thm.det.vander)

The Vandermonde determinant is a classical result: the determinant of a matrix
with entries aᵢʲ⁻¹ (or variants) equals a product of differences.

The proof uses "factor hunting": we show the determinant is divisible by each
(aᵢ - aⱼ) for i < j, and then compare degrees to conclude equality up to a constant,
which is determined by examining the leading coefficient.
-/


/-- The Vandermonde matrix with entries `a i ^ (n - 1 - j)` for 0-indexed i, j.
    This corresponds to the matrix (aᵢⁿ⁻ʲ) in 1-indexed notation.
    Label: thm.det.vander -/
def vandermondeMat (a : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => a i ^ (n - 1 - j.val)

/-- The standard Vandermonde matrix with entries `a i ^ j`.
    This corresponds to the matrix (aᵢʲ⁻¹) in 1-indexed notation. -/
def vandermondeMat' (a : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => a i ^ j.val

/-!
## Lemma lem.det.vander.a.pol - Vandermonde determinant in polynomial ring

This is a key lemma that establishes the Vandermonde identity for polynomial indeterminates.
The general Vandermonde theorem (thm.det.vander) follows from this by substitution.

The proof relates our matrix convention to Mathlib's via column reversal, and uses the
fact that swapping the order of subtraction in each factor introduces a sign that
cancels with the sign from the column permutation.
-/

/-- The Vandermonde matrix in the polynomial ring ℤ[x₁,...,xₙ] with entries xᵢⁿ⁻ʲ.
    This is the matrix from Lemma lem.det.vander.a.pol.
    Entry (i,j) = xᵢ^{n-1-j} (using 0-indexed notation).
    Label: lem.det.vander.a.pol -/
noncomputable def vandermondePolyMat (m : ℕ) : Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) ℤ) :=
  Matrix.of fun i j => (MvPolynomial.X i) ^ (m - 1 - j.val)

/-- The product of differences ∏_{1≤i<j≤n} (xᵢ - xⱼ) in the polynomial ring.
    Label: lem.det.vander.a.pol -/
noncomputable def vandermondePolyProd (m : ℕ) : MvPolynomial (Fin m) ℤ :=
  ∏ i : Fin m, ∏ j ∈ Ioi i, (MvPolynomial.X i - MvPolynomial.X j)

/-!
## Proposition prop.det.(xi+yj)n-1

The determinant of the matrix ((xᵢ + yⱼ)ⁿ⁻¹) can be expressed as a product of
binomial coefficients and Vandermonde-like products.
-/


/-- The matrix with entries (xᵢ + yⱼ)ⁿ⁻¹.
    Label: prop.det.(xi+yj)n-1 -/
def sumPowMat (x y : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (x i + y j) ^ (n - 1)

/-- Helper matrix P for the factorization: P_{i,k} = C(n-1,k) * x_i^k -/
def matP (x : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i k => (n - 1).choose k.val * x i ^ k.val

/-- Helper matrix Q for the factorization: Q_{k,j} = y_j^{n-1-k} -/
def matQ (y : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun k j => y j ^ (n - 1 - k.val)

/-!
## Laplace Expansion (Theorem thm.det.laplace)

Laplace expansion expresses a determinant as a sum over cofactors along
any row or column.
-/


/-- Convention conv.mat.tilde: A_{~i,~j} denotes the submatrix obtained by
    removing row i and column j.

    In Mathlib, this is `Matrix.submatrix A (Fin.succAbove i) (Fin.succAbove j)`
    for an (n+1)×(n+1) matrix A, yielding an n×n matrix. -/
def submatrixRemove {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R)
    (i j : Fin (m + 1)) : Matrix (Fin m) (Fin m) R :=
  A.submatrix i.succAbove j.succAbove

/-!
## Proposition prop.det.laplace.0

When we use entries from a different row/column than the one we're expanding along,
the sum is zero.
-/
/-!
## Adjugate Matrix (Definition def.det.adj)

The adjugate (classical adjoint) of a matrix A is defined by
(adj A)_{i,j} = (-1)^(i+j) det(A_{~j,~i})

Note the index swap: the (i,j) entry involves removing row j and column i.
-/


/-- The adjugate matrix (Definition def.det.adj).

    The adjugate (or classical adjoint) of an n×n matrix A is the n×n matrix whose (i,j) entry is
    (-1)^(i+j) times the determinant of the (n-1)×(n-1) submatrix obtained by deleting row j and
    column i from A. Note the index swap: the (i,j) entry involves removing row j and column i.

    The key property is: A · adj(A) = adj(A) · A = det(A) · I

    Note: Mathlib defines `Matrix.adjugate` which is the same concept, but using a different
    but equivalent definition. We provide this definition for clarity and connection to the textbook.
    Label: def.det.adj -/
def adjugateMat {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => (-1) ^ (i.val + j.val) * (submatrixRemove A j i).det

/-!
## Theorem thm.det.adj.inverse

The fundamental property of the adjugate matrix: multiplication by the adjugate
yields the determinant times the identity matrix.

**Theorem Statement**: Let n ∈ ℕ. Let A ∈ K^{n×n} be an n×n matrix.
Let I_n denote the n×n identity matrix. Then:
  A · (adj A) = (adj A) · A = (det A) · I_n

**Proof Sketch** (from the textbook):
To show A · (adj A) = (det A) · I_n, we check that the (i,j)-th entry of A · (adj A)
equals det A when i = j, and equals 0 otherwise.

- Case i = j: This follows from Laplace expansion along row i (Theorem thm.det.laplace (a)).
  The (i,i) entry of A · (adj A) is ∑_k A_{i,k} · (adj A)_{k,i} = ∑_k A_{i,k} · (-1)^{i+k} · det(A_{~i,~k})
  which equals det A by Laplace expansion.

- Case i ≠ j: This follows from Proposition prop.det.laplace.0 (a).
  The (i,j) entry of A · (adj A) is ∑_k A_{i,k} · (adj A)_{k,j} = ∑_k A_{i,k} · (-1)^{j+k} · det(A_{~j,~k})
  which equals 0 because we're using row i entries with row j cofactors.

Similarly, (adj A) · A = (det A) · I_n can be shown using column versions.
-/
/-!
## Laplace Expansion Along Multiple Rows/Columns (Theorem thm.det.laplace-multi)

This generalizes Laplace expansion to expanding along multiple rows or columns
simultaneously.

For a subset P of row indices, the determinant can be expanded as a sum over all
column subsets Q of the same size, involving products of complementary minors.
-/


/-- Helper: Given a finset of indices, produce an order-preserving embedding into Fin m.
    This is used to extract submatrices corresponding to index subsets. -/
noncomputable def finsetToFin {m k : ℕ} (S : Finset (Fin m)) (hk : S.card = k) :
    Fin k ↪ Fin m :=
  (Finset.orderIsoOfFin S hk).toEmbedding.trans (Function.Embedding.subtype _)

/-- The submatrix of A with rows from P and columns from Q (when |P| = |Q|).
    This is the minor sub_P^Q(A) in the source notation. -/
noncomputable def submatrixOfFinsets' {m k : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (P Q : Finset (Fin m)) (hP : P.card = k) (hQ : Q.card = k) :
    Matrix (Fin k) (Fin k) R :=
  A.submatrix (finsetToFin P hP) (finsetToFin Q hQ)

/-- The determinant of a submatrix corresponding to row set P and column set Q.
    Returns 0 if |P| ≠ |Q|. -/
noncomputable def submatrixDet {m : ℕ} (A : Matrix (Fin m) (Fin m) R)
    (P Q : Finset (Fin m)) : R :=
  if h : P.card = Q.card then
    (submatrixOfFinsets' A P Q rfl h.symm).det
  else 0

/-- The set of column subsets Q with |Q| = |P|. -/
def sameCardSubsets (m : ℕ) (P : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  Finset.filter (fun Q => Q.card = P.card) (Finset.univ.powerset)

end Determinants
end AlgebraicCombinatorics
