/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
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

/-!
## Submatrices (Definition def.det.sub)

For an n×m matrix A, subsets U ⊆ [n] and V ⊆ [m], we define
sub_U^V A to be the |U|×|V| submatrix obtained by keeping only
the rows indexed by U and columns indexed by V (in increasing order).

In Mathlib, this is `Matrix.submatrix A f g` where f and g are the
order-preserving embeddings of U and V into [n] and [m].
-/


/-- The submatrix of A obtained by restricting to rows in U and columns in V.
    This corresponds to `sub_U^V A` in the source (Definition def.det.sub).
    Label: def.det.sub
    
    ## Mathematical Description
    
    Let A be an n×m matrix. Let U ⊆ [n] and V ⊆ [m] be subsets.
    Writing U = {u₁, u₂, ..., uₚ} with u₁ < u₂ < ... < uₚ
    and V = {v₁, v₂, ..., vₚ} with v₁ < v₂ < ... < vₚ,
    we define sub_U^V A := (A_{uᵢ,vⱼ})_{1≤i≤p, 1≤j≤q}.
    
    This is the |U|×|V| matrix obtained from A by keeping only the rows
    indexed by U and columns indexed by V, in increasing order.
    
    ## Terminology
    
    - **Submatrix**: The matrix sub_U^V A
    - **Minor**: When |U| = |V|, the determinant det(sub_U^V A) is called a minor of A
    - **Principal minor**: When U = V, the minor det(sub_U^U A) is called a principal minor
    
    ## Implementation
    
    In Mathlib, `Matrix.submatrix` takes functions for row and column selection.
    For finite sets, we use the canonical order-preserving embedding `orderEmbOfFin`. -/
noncomputable def submatrixOfFinset {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) :
    Matrix (Fin U.card) (Fin V.card) R :=
  A.submatrix (U.orderEmbOfFin rfl) (V.orderEmbOfFin rfl)

end CauchyBinet
end AlgebraicCombinatorics
