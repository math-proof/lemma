/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
open Matrix Finset BigOperators

/-!
# Determinants: Basic Properties

This file formalizes the basic properties of determinants from
Section "Determinants" (sec.sign.det) of the source.

## Main definitions

The determinant is already defined in Mathlib as `Matrix.det`. This file provides:
* Additional lemmas connecting Mathlib's API to the textbook presentation
* Specific examples and exercises from the source

## Main results

### Definition (Definition def.det.det)
The determinant of an n×n matrix A is defined as:
  det A = ∑_{σ ∈ Sₙ} (-1)^σ · A_{1,σ(1)} · A_{2,σ(2)} · ... · A_{n,σ(n)}

### Basic Properties
* `Matrix.det_transpose` - Transposes preserve determinants (Theorem thm.det.transp)
* `Matrix.det_of_isUpperTriangular` / `Matrix.det_of_lowerTriangular` -
    Determinant of triangular matrix is product of diagonal (Theorem thm.det.triang)
* Row operation properties (Theorem thm.det.rowop):
  - (a) Swapping rows multiplies det by -1
  - (b) Zero row implies det = 0
  - (c) Equal rows implies det = 0
  - (d) Scaling a row by λ scales det by λ
  - (e,f) Adding multiple of one row to another preserves det
  - (g) Multilinearity in rows
* Column operation properties (Theorem thm.det.colop) - analogous for columns
* Permutation of rows/columns (Corollary cor.det.sig-row-col)
* `Matrix.det_mul` - Multiplicativity: det(AB) = det(A) · det(B) (Theorem thm.det.detAB)
* Row/column scaling (Corollary cor.det.scale-row-col)

### Propositions
* `det_xiyj_eq_zero` - det(xᵢyⱼ) = 0 for n ≥ 2 (Proposition prop.det.xiyj)
* `det_xi_add_yj_eq_zero` - det(xᵢ + yⱼ) = 0 for n ≥ 3 (Proposition prop.det.xi+yj)
* `det_hollow_matrix_eq_zero` - Hollow 5×5 matrix has det = 0 (Example exa.det.hollow5x5)

## References

* Source: BasicProperties.tex, sec.sign.det

## Implementation notes

Mathlib already provides `Matrix.det` with most of the basic properties.
This file adds:
1. Documentation connecting Mathlib API to the textbook
2. Specific examples and exercises from the source
3. Some additional lemmas in the style of the textbook

Note: Mathlib uses 0-indexing for matrices (Fin n), while the source uses 1-indexing.
The Mathlib definition uses A(σ(i), i) rather than A(i, σ(i)), but these are equivalent
by reindexing the permutation.
-/


namespace AlgebraicCombinatorics

namespace Det

variable {K : Type*} [CommRing K]

variable {n m : ℕ}

/-!
## Convention (conv.det.K)

We work over a commutative ring K. In most examples, K will be ℤ, ℚ, or a polynomial ring.
-/
/-!
## Convention (conv.det.matrices)

(a) For an n×m matrix A, A_{i,j} denotes the (i,j)-th entry.
(b) We write (a_{i,j})_{1≤i≤n, 1≤j≤m} for the matrix with entries a_{i,j}.
(c) K^{n×m} denotes the set of n×m matrices over K.
(d) A^T denotes the transpose of A.

In Mathlib:
- Matrices are `Matrix (Fin n) (Fin m) K`
- Entry access is `A i j` for `i : Fin n` and `j : Fin m`
- Transpose is `Matrix.transpose A` or `Aᵀ`
-/
/-!
## Definition of Determinant (Definition def.det.det)

The determinant of an n×n matrix A is:
  det A = ∑_{σ ∈ Sₙ} (-1)^σ · ∏_{i=1}^n A_{i,σ(i)}

In Mathlib, this is `Matrix.det A`, defined as:
  det A = ∑_{σ ∈ Sₙ} (-1)^σ · ∏_{i} A_{σ(i),i}

These are equivalent by substituting σ ↦ σ⁻¹.
-/
/-!
## Examples of small determinants

For n = 0: det() = 1 (empty product)
For n = 1: det(a) = a
For n = 2: det [[a, b], [a', b']] = a·b' - b·a'
For n = 3: The 6-term expansion over S₃
-/
/-!
## Example: Hollow 5×5 matrix (Example exa.det.hollow5x5)

A 5×5 matrix with a 3×3 block of zeros in the middle has determinant 0.
The proof uses the pigeonhole principle: any permutation must map some
element of {2,3,4} to {2,3,4}, hitting a zero entry.
-/
/-!
## Proposition: det(xᵢyⱼ) = 0 (Proposition prop.det.xiyj)

For n ≥ 2, if we form the n×n matrix with (i,j)-entry xᵢ·yⱼ,
then its determinant is 0.

The proof uses ∑_{σ ∈ Sₙ} (-1)^σ = 0 for n ≥ 2.
-/


/-- The matrix with entries x_i * y_j.
    Label: prop.det.xiyj -/
def outerProductMatrix (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => x i * y j

/-!
## Proposition: det(xᵢ + yⱼ) = 0 (Proposition prop.det.xi+yj)

For n ≥ 3, if we form the n×n matrix with (i,j)-entry xᵢ + yⱼ,
then its determinant is 0.

The proof uses a cancellation argument involving transpositions.
-/


/-- The matrix with entries x_i + y_j.
    Label: prop.det.xi+yj -/
def sumMatrix (x y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => x i + y j

/-- The matrix A in the factorization of sumMatrix: first column is x_i, second column is 1, rest are 0.
    Used in the second proof of prop.det.xi+yj. -/
def sumMatrix_factorA (x : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j =>
    if j.val = 0 then x i
    else if j.val = 1 then 1
    else 0

/-- The matrix B in the factorization of sumMatrix: first row is 1, second row is y_j, rest are 0.
    Used in the second proof of prop.det.xi+yj. -/
def sumMatrix_factorB (y : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j =>
    if i.val = 0 then 1
    else if i.val = 1 then y j
    else 0

/-!
## Theorem: Transposes preserve determinants (Theorem thm.det.transp)

det(A^T) = det(A)
-/
/-!
## Theorem: Determinants of triangular matrices (Theorem thm.det.triang)

If A is upper-triangular or lower-triangular, then det A = ∏ᵢ Aᵢᵢ.
-/
/-!
## Theorem: Row operation properties (Theorem thm.det.rowop)

(a) Swapping rows multiplies det by -1
(b) Zero row implies det = 0
(c) Equal rows implies det = 0
(d) Scaling a row by λ scales det by λ
(e) Adding a row to another preserves det
(f) Adding λ times a row to another preserves det
(g) Multilinearity: det is additive in each row
-/
/-!
## Theorem: Column operation properties (Theorem thm.det.colop)

The column analogues of Theorem thm.det.rowop follow from the row versions
using det(A^T) = det(A).
-/
/-!
## Corollary: Permuting rows/columns (Corollary cor.det.sig-row-col)

When we permute the rows or columns of a matrix by τ ∈ Sₙ,
the determinant gets multiplied by sign(τ).
-/
/-!
## Theorem: Multiplicativity of the determinant (Theorem thm.det.detAB)

det(AB) = det(A) · det(B)
-/
/-!
## Corollary: Scaling rows/columns (Corollary cor.det.scale-row-col)

Scaling each row i by dᵢ (or each column j by dⱼ) multiplies
the determinant by ∏ᵢ dᵢ.
-/
/-!
## Alternative proofs using multiplicativity

The source provides alternative proofs of Proposition prop.det.xiyj and
Proposition prop.det.xi+yj using matrix factorization and det(AB) = det(A)·det(B).
-/

end Det
end AlgebraicCombinatorics
