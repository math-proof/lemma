/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.Data.Fin.SkipTwo
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Lemma.Finset.PermFinset
import Def.LinearAlgebra.Matrix.Determinant.DesnanotJacobi.Part6
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
### Properties of skipTwo

These lemmas are aliases for the corresponding lemmas in `AlgebraicCombinatorics.Fin.SkipTwo`.
-/
/-!
### Helper lemmas for skipTwo in Fin 4

These simp lemmas allow efficient computation of `skipTwo` values for all valid
(p, q) pairs in Fin 4. There are 6 such pairs: (0,1), (0,2), (0,3), (1,2), (1,3), (2,3).
-/
@[simp] theorem skipTwo_4_01_0 (h : (0 : Fin 4) < 1) : skipTwo 0 1 h (0 : Fin 2) = 2 := by
  simp only [Fin.skipTwo, Fin.val_zero, Fin.val_one]; decide

@[simp] theorem skipTwo_4_01_1 (h : (0 : Fin 4) < 1) : skipTwo 0 1 h (1 : Fin 2) = 3 := by
  simp only [Fin.skipTwo, Fin.val_zero, Fin.val_one]; decide

@[simp] theorem skipTwo_4_02_0 (h : (0 : Fin 4) < 2) : skipTwo 0 2 h (0 : Fin 2) = 1 := by
  simp only [Fin.skipTwo, Fin.val_zero]; decide

@[simp] theorem skipTwo_4_02_1 (h : (0 : Fin 4) < 2) : skipTwo 0 2 h (1 : Fin 2) = 3 := by
  simp only [Fin.skipTwo, Fin.val_zero, Fin.val_one]; decide

@[simp] theorem skipTwo_4_03_0 (h : (0 : Fin 4) < 3) : skipTwo 0 3 h (0 : Fin 2) = 1 := by
  simp only [Fin.skipTwo, Fin.val_zero]; decide

@[simp] theorem skipTwo_4_03_1 (h : (0 : Fin 4) < 3) : skipTwo 0 3 h (1 : Fin 2) = 2 := by
  simp only [Fin.skipTwo, Fin.val_zero, Fin.val_one]; decide

@[simp] theorem skipTwo_4_12_0 (h : (1 : Fin 4) < 2) : skipTwo 1 2 h (0 : Fin 2) = 0 := by
  simp only [Fin.skipTwo, Fin.val_zero, Fin.val_one]; decide

@[simp] theorem skipTwo_4_12_1 (h : (1 : Fin 4) < 2) : skipTwo 1 2 h (1 : Fin 2) = 3 := by
  simp only [Fin.skipTwo, Fin.val_one]; decide

@[simp] theorem skipTwo_4_13_0 (h : (1 : Fin 4) < 3) : skipTwo 1 3 h (0 : Fin 2) = 0 := by
  simp only [Fin.skipTwo, Fin.val_zero, Fin.val_one]; decide

@[simp] theorem skipTwo_4_13_1 (h : (1 : Fin 4) < 3) : skipTwo 1 3 h (1 : Fin 2) = 2 := by
  simp only [Fin.skipTwo, Fin.val_one]; decide

@[simp] theorem skipTwo_4_23_0 (h : (2 : Fin 4) < 3) : skipTwo 2 3 h (0 : Fin 2) = 0 := by
  simp only [Fin.skipTwo, Fin.val_zero]; decide

@[simp] theorem skipTwo_4_23_1 (h : (2 : Fin 4) < 3) : skipTwo 2 3 h (1 : Fin 2) = 1 := by
  simp only [Fin.skipTwo, Fin.val_one]; decide

/-!
### Helper lemmas for Fin.succAbove in Fin 4

These simp lemmas allow efficient computation of `Fin.succAbove` for Fin 4.
-/

-- Tactic for proving individual 4x4 Desnanot-Jacobi cases by expansion.


@[simp] theorem succAbove_4_0_0 : Fin.succAbove (0 : Fin 4) (0 : Fin 3) = 1 := rfl

@[simp] theorem succAbove_4_0_1 : Fin.succAbove (0 : Fin 4) (1 : Fin 3) = 2 := rfl

@[simp] theorem succAbove_4_0_2 : Fin.succAbove (0 : Fin 4) (2 : Fin 3) = 3 := rfl

@[simp] theorem succAbove_4_1_0 : Fin.succAbove (1 : Fin 4) (0 : Fin 3) = 0 := rfl

@[simp] theorem succAbove_4_1_1 : Fin.succAbove (1 : Fin 4) (1 : Fin 3) = 2 := rfl

@[simp] theorem succAbove_4_1_2 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = 3 := rfl

@[simp] theorem succAbove_4_2_0 : Fin.succAbove (2 : Fin 4) (0 : Fin 3) = 0 := rfl

@[simp] theorem succAbove_4_2_1 : Fin.succAbove (2 : Fin 4) (1 : Fin 3) = 1 := rfl

@[simp] theorem succAbove_4_2_2 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := rfl

@[simp] theorem succAbove_4_3_0 : Fin.succAbove (3 : Fin 4) (0 : Fin 3) = 0 := rfl

@[simp] theorem succAbove_4_3_1 : Fin.succAbove (3 : Fin 4) (1 : Fin 3) = 1 := rfl

@[simp] theorem succAbove_4_3_2 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := rfl

/-- Helper lemma: 4×4 determinant expansion formula.
    Used for proving the 4×4 case of desnanot_jacobi_direct. -/
theorem det_fin_four_expand (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) -
               A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) +
               A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1)) -
      A 0 1 * (A 1 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) -
               A 1 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0) +
               A 1 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0)) +
      A 0 2 * (A 1 0 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) -
               A 1 1 * (A 2 0 * A 3 3 - A 2 3 * A 3 0) +
               A 1 3 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) -
      A 0 3 * (A 1 0 * (A 2 1 * A 3 2 - A 2 2 * A 3 1) -
               A 1 1 * (A 2 0 * A 3 2 - A 2 2 * A 3 0) +
               A 1 2 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) := by
  simp only [det_succ_column A 0, Fin.sum_univ_four, det_fin_three, submatrix_apply]
  have ha00 : Fin.succAbove (0 : Fin 4) (0 : Fin 3) = (1 : Fin 4) := rfl
  have ha01 : Fin.succAbove (0 : Fin 4) (1 : Fin 3) = (2 : Fin 4) := rfl
  have ha02 : Fin.succAbove (0 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := rfl
  have ha10 : Fin.succAbove (1 : Fin 4) (0 : Fin 3) = (0 : Fin 4) := rfl
  have ha11 : Fin.succAbove (1 : Fin 4) (1 : Fin 3) = (2 : Fin 4) := rfl
  have ha12 : Fin.succAbove (1 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := rfl
  have ha20 : Fin.succAbove (2 : Fin 4) (0 : Fin 3) = (0 : Fin 4) := rfl
  have ha21 : Fin.succAbove (2 : Fin 4) (1 : Fin 3) = (1 : Fin 4) := rfl
  have ha22 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = (3 : Fin 4) := rfl
  have ha30 : Fin.succAbove (3 : Fin 4) (0 : Fin 3) = (0 : Fin 4) := rfl
  have ha31 : Fin.succAbove (3 : Fin 4) (1 : Fin 3) = (1 : Fin 4) := rfl
  have ha32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = (2 : Fin 4) := rfl
  simp only [ha00, ha01, ha02, ha10, ha11, ha12, ha20, ha21, ha22, ha30, ha31, ha32]
  have hv2 : (2 : Fin 4).val = 2 := rfl
  have hv3 : (3 : Fin 4).val = 3 := rfl
  simp only [Fin.val_zero, Fin.val_one, hv2, hv3, pow_succ, pow_zero, one_mul, neg_one_mul]
  ring

end Determinants
end AlgebraicCombinatorics
