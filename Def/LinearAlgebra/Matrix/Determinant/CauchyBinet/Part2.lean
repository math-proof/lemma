/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Notation.LinearAlgebra.Matrix.Determinant.CauchyBinet
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

/-- A **minor** of a matrix A is the determinant of a square submatrix.
    This is det(sub_U^V A) where |U| = |V|.
    
    If |U| ≠ |V|, we define the minor to be 0 (since the submatrix is not square). -/
noncomputable def minor {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (U : Finset (Fin n)) (V : Finset (Fin m)) : R :=
  if h : U.card = V.card then
    (A.submatrix (U.orderEmbOfFin rfl) (V.orderEmbOfFin (h ▸ rfl))).det
  else 0

/-- A **principal minor** of a square matrix is a minor where U = V.
    These are the determinants of principal submatrices (same rows and columns). -/
noncomputable def principalMinor {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P : Finset (Fin n)) : R :=
  (A.submatrix (P.orderEmbOfFin rfl) (P.orderEmbOfFin rfl)).det

end CauchyBinet
end AlgebraicCombinatorics
