/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Def.LinearAlgebra.Matrix.Determinant.CauchyBinet.Part3
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

/-! ### Helper lemmas for the key factorization

The proof of `sum_perms_mapping_eq_det_product` requires:
1. A bijection between {σ : σ(P) = Q} and Perm(Fin |P|) × Perm(Fin |Pᶜ|)
2. A sign identity: sign(σ) = (-1)^(sum P + sum Q) · sign(α) · sign(β)
3. Product factorization into determinants

We build these up step by step.
-/


/-- For σ with σ(P) = Q, the image of any element of P under σ lies in Q. -/
theorem sigma_orderEmb_mem_of_imageFinset {n : ℕ} (P Q : Finset (Fin n)) 
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) (i : Fin P.card) :
    σ (P.orderEmbOfFin rfl i) ∈ Q := by
  rw [← hσ]
  simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk]
  exact ⟨P.orderEmbOfFin rfl i, Finset.orderEmbOfFin_mem P rfl i, rfl⟩

/-- For σ with σ(P) = Q, the image of any element of Pᶜ under σ lies in Qᶜ. -/
theorem sigma_orderEmb_compl_mem_of_imageFinset {n : ℕ} (P Q : Finset (Fin n)) 
    (σ : Equiv.Perm (Fin n)) (hσ : imageFinset σ P = Q) (i : Fin Pᶜ.card) :
    σ (Pᶜ.orderEmbOfFin rfl i) ∈ Qᶜ := by
  simp only [Finset.mem_compl]
  intro hcontra
  rw [← hσ] at hcontra
  simp only [imageFinset, Finset.mem_map, Function.Embedding.coeFn_mk] at hcontra
  obtain ⟨p, hp, hσp⟩ := hcontra
  have : Pᶜ.orderEmbOfFin rfl i ∈ P := by
    have h := σ.injective hσp
    rw [← h]
    exact hp
  have hmem : Pᶜ.orderEmbOfFin rfl i ∈ Pᶜ := Finset.orderEmbOfFin_mem Pᶜ rfl i
  exact (Finset.mem_compl.mp hmem) this

end CauchyBinet
end AlgebraicCombinatorics
