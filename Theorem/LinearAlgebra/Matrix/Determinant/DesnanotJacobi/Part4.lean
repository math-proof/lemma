/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Data.Fin.SkipTwo
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Lemma.Finset.PermFinset
import Def.LinearAlgebra.Matrix.Determinant.DesnanotJacobi.Part4
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

/-! ### Helper lemmas for Desnanot-Jacobi -/
/-!
## Helper lemmas for Fin.succAbove computations in 6×6 matrices

These lemmas are used to convert `Fin.succAbove` indices to concrete values
when expanding determinants. Each lemma states that `Fin.succAbove i j` equals
a specific concrete value for `i : Fin 6` and `j : Fin 5`.
-/

/-- Verification that the Desnanot-Jacobi identity holds for 6×6 matrices.
    These tests confirm the identity is correct via native_decide on specific matrices. -/
example :
  let A : Matrix (Fin 6) (Fin 6) ℤ := !![1, 2, 3, 4, 5, 6; 
                                         7, 8, 9, 10, 11, 12;
                                         13, 14, 15, 16, 17, 18;
                                         19, 20, 21, 22, 23, 24;
                                         25, 26, 27, 28, 29, 30;
                                         31, 32, 33, 34, 35, 36]
  A.det * (innerSubmatrix A).det =
    (submatrixRemove A 0 0).det * (submatrixRemove A (Fin.last 5) (Fin.last 5)).det -
    (submatrixRemove A 0 (Fin.last 5)).det * (submatrixRemove A (Fin.last 5) 0).det := by
  native_decide

example :
  let A : Matrix (Fin 6) (Fin 6) ℤ := !![3, 1, 4, 1, 5, 9; 
                                         2, 6, 5, 3, 5, 8;
                                         9, 7, 9, 3, 2, 3;
                                         8, 4, 6, 2, 6, 4;
                                         3, 3, 8, 3, 2, 7;
                                         9, 5, 0, 2, 8, 8]
  A.det * (innerSubmatrix A).det =
    (submatrixRemove A 0 0).det * (submatrixRemove A (Fin.last 5) (Fin.last 5)).det -
    (submatrixRemove A 0 (Fin.last 5)).det * (submatrixRemove A (Fin.last 5) 0).det := by
  native_decide

end Determinants
end AlgebraicCombinatorics
