/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.LinearAlgebra.Matrix.Determinant.PermFinset
import Theorem.LinearAlgebra.Matrix.Determinant.CauchyBinet
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
## Cauchy-Binet Formula (Theorem thm.det.CB)

For an n×m matrix A and an m×n matrix B:
  det(AB) = ∑_{g : strictly increasing n-tuple from [m]} det(cols_g A) · det(rows_g B)

This generalizes det(AB) = det(A)·det(B) for square matrices.

Special cases:
- If m < n, the sum is empty, so det(AB) = 0
- If m = n, there's only one term: det(A)·det(B)
-/

/-- Submatrix obtained by selecting specific columns of A.
    `cols_g A` in the source notation selects columns indexed by g. -/
noncomputable def colsSubmatrix {n m : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (S : Finset (Fin m)) (hcard : S.card = n) : Matrix (Fin n) (Fin n) R :=
  A.submatrix id (S.orderEmbOfFin hcard)

/-- Submatrix obtained by selecting specific rows of B.
    `rows_g B` in the source notation selects rows indexed by g. -/
noncomputable def rowsSubmatrix {n m : ℕ} (B : Matrix (Fin m) (Fin n) R)
    (S : Finset (Fin m)) (hcard : S.card = n) : Matrix (Fin n) (Fin n) R :=
  B.submatrix (S.orderEmbOfFin hcard) id

/-!
## Determinant of A + B (Theorem thm.det.det(A+B))

For n×n matrices A and B:
  det(A+B) = ∑_{P ⊆ [n]} ∑_{Q ⊆ [n], |P|=|Q|} (-1)^(sum P + sum Q) · det(sub_P^Q A) · det(sub_P̃^Q̃ B)

where P̃ denotes the complement [n] \ P.

This is a "binomial theorem" for determinants, containing det(A) (P=Q=[n])
and det(B) (P=Q=∅) as special terms.
-/


/-- Sum of elements in a finset of Fin n, viewed as natural numbers.
    Used in the sign factor of the det(A+B) formula.

    Note: This is named `finsetSumFin` to distinguish from `AlgebraicCombinatorics.QBinomialRec.finsetSumNat`,
    which computes the sum of elements in a `Finset ℕ` directly.
    Both compute "the sum of elements" but for different element types. -/
def finsetSumFin {n : ℕ} (P : Finset (Fin n)) : ℕ := ∑ i ∈ P, i.val

/-- Helper: Given P, Q with same cardinality, compute the determinant of the
    submatrix of A restricted to rows P and columns Q. -/
noncomputable def submatrixDet {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (P Q : Finset (Fin n)) (h : P.card = Q.card) : R :=
  (A.submatrix (P.orderEmbOfFin rfl) (Q.orderEmbOfFin (h ▸ rfl))).det

/-! ### Proof infrastructure for det(A+B) formula

The proof proceeds in several steps:
1. Expand det(A+B) using the Leibniz formula
2. Use the product rule ∏(a+b) = ∑_P (∏_{i∈P} a_i)(∏_{i∈Pᶜ} b_i)
3. Swap the order of summation
4. Partition the sum over σ based on σ(P) = Q
5. Factor out the sign and show it equals (-1)^(sum P + sum Q)
6. Recognize the remaining sums as determinants of submatrices
-/
/-!
### Permutation image definitions

These are local definitions that duplicate the bodies of the canonical definitions in 
`PermFinset` namespace (`Determinants/PermFinset.lean`). The definitions are 
**definitionally equal** to their `PermFinset` counterparts (witnessed by 
`imageFinset_eq_permFinset` and `permsMapping_eq_permFinset`), but are kept as 
separate `def`s rather than wrappers because many proofs in this file rely on 
specific unfolding behavior with `simp [imageFinset]`.

**For new code**: Use `PermFinset.imageFinset` and `PermFinset.permsMapping` directly.
-/


/-- The image of a finset under a permutation.
    
    This is definitionally equal to `PermFinset.imageFinset` (see `imageFinset_eq_permFinset`).
    New code should prefer `PermFinset.imageFinset`. -/
def imageFinset {n : ℕ} (σ : Equiv.Perm (Fin n)) (P : Finset (Fin n)) : Finset (Fin n) :=
  P.map ⟨σ, σ.injective⟩

/-- The set of permutations that map P to Q.
    
    This is definitionally equal to `PermFinset.permsMapping` (see `permsMapping_eq_permFinset`).
    New code should prefer `PermFinset.permsMapping`. -/
def permsMapping {n : ℕ} (P Q : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => imageFinset σ P = Q)

end CauchyBinet
end AlgebraicCombinatorics
