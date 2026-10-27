/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Def.LinearAlgebra.Matrix.Determinant.CauchyBinet.Part2
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

/-- Example: For a 3×3 matrix, sub_{0,1}^{0,2} A extracts the 2×2 submatrix
    with rows 0,1 and columns 0,2.
    
    For the matrix:
      (a   b   c  )
      (a'  b'  c' )
      (a'' b'' c'')
    
    we get sub_{0,1}^{0,2} A = (a   c )
                               (a'  c')
    
    Note: The textbook uses 1-indexing, so sub_{1,2}^{1,3} in the textbook
    corresponds to sub_{0,1}^{0,2} in our 0-indexed formalization. -/
example {A : Matrix (Fin 3) (Fin 3) R} :
    let U : Finset (Fin 3) := {0, 1}
    let V : Finset (Fin 3) := {0, 2}
    submatrixOfFinset A U V = A.submatrix (U.orderEmbOfFin rfl) (V.orderEmbOfFin rfl) := rfl

end CauchyBinet
end AlgebraicCombinatorics
