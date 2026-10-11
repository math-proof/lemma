import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DeterminantsBasic


/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_eq_sum_sign_prod_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K) :
-- imply
  A.det = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A (σ i) i := by
-- proof
  apply AlgebraicCombinatorics.Det.det_eq_sum_sign_prod A

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_eq_sum_sign_prod_textbook_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K) :
-- imply
  A.det = ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, A i (σ i) := by
-- proof
  apply AlgebraicCombinatorics.Det.det_eq_sum_sign_prod_textbook A

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_fin_zero_eq
  [CommRing K]
-- given
  (A : Matrix (Fin 0) (Fin 0) K) :
-- imply
  A.det = 1 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_fin_zero' A

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_fin_one_eq
  [CommRing K]
-- given
  (A : Matrix (Fin 1) (Fin 1) K) :
-- imply
  A.det = A 0 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_fin_one' A

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_fin_two_eq
  [CommRing K]
-- given
  (A : Matrix (Fin 2) (Fin 2) K) :
-- imply
  A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_fin_two' A

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_one_eq_one_eq
  [CommRing K] :
-- imply
  Matrix.det (1 : Matrix (Fin n) (Fin n) K) = 1 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_one_eq_one

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_zero_eq_zero_eq
  [CommRing K]
-- given
  (hn : 0 < n) :
-- imply
  Matrix.det (0 : Matrix (Fin n) (Fin n) K) = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_zero_eq_zero hn

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_hollow_core_eq_zero_eq
  [CommRing K]
-- given
  (A : Matrix (Fin 5) (Fin 5) K)
  (hA : ∀ i j : Fin 5, i.val ∈ ({1, 2, 3} : Set ℕ) → j.val ∈ ({1, 2, 3} : Set ℕ) →
    A i j = 0) :
-- imply
  A.det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_hollow_core_eq_zero A hA

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma outer_product_matrix_apply_eq
  [CommRing K]
-- given
  (x y : Fin n → K)
  (i j : Fin n) :
-- imply
  AlgebraicCombinatorics.Det.outerProductMatrix x y i j = x i * y j := by
-- proof
  apply AlgebraicCombinatorics.Det.outerProductMatrix_apply x y i j

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma sum_sign_eq_zero_eq
  [CommRing K]
-- given
  (hn : 2 ≤ n) :
-- imply
  ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : K) = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.sum_sign_eq_zero hn

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_outer_product_eq_zero_eq
  [CommRing K]
-- given
  (hn : 2 ≤ n)
  (x y : Fin n → K) :
-- imply
  (AlgebraicCombinatorics.Det.outerProductMatrix x y).det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_outerProduct_eq_zero x y hn

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_const_matrix_eq_zero_eq
  [CommRing K]
-- given
  (hn : 2 ≤ n)
  (c : K) :
-- imply
  (Matrix.of fun _ _ : Fin n => c).det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_const_matrix_eq_zero c hn

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma sum_matrix_apply_eq
  [CommRing K]
-- given
  (x y : Fin n → K)
  (i j : Fin n) :
-- imply
  AlgebraicCombinatorics.Det.sumMatrix x y i j = x i + y j := by
-- proof
  apply AlgebraicCombinatorics.Det.sumMatrix_apply x y i j

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma sum_matrix_factor_a_has_zero_col_eq
  [CommRing K]
-- given
  (hn : 3 ≤ n)
  (x : Fin n → K) :
-- imply
  ∀ i, (AlgebraicCombinatorics.Det.sumMatrix_factorA x) i ⟨2, by omega⟩ = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.sumMatrix_factorA_has_zero_col x hn

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_sum_matrix_factor_a_eq_zero_eq
  [CommRing K]
-- given
  (hn : 3 ≤ n)
  (x : Fin n → K) :
-- imply
  (AlgebraicCombinatorics.Det.sumMatrix_factorA x).det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_sumMatrix_factorA_eq_zero x hn

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma sum_matrix_eq_factor_a_mul_factor_b_eq
  [CommRing K]
-- given
  (hn : 2 ≤ n)
  (x y : Fin n → K) :
-- imply
  AlgebraicCombinatorics.Det.sumMatrix x y =
    AlgebraicCombinatorics.Det.sumMatrix_factorA x *
      AlgebraicCombinatorics.Det.sumMatrix_factorB y := by
-- proof
  apply AlgebraicCombinatorics.Det.sumMatrix_eq_factorA_mul_factorB x y hn

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_sum_matrix_eq_zero_eq
  [CommRing K]
-- given
  (hn : 3 ≤ n)
  (x y : Fin n → K) :
-- imply
  (AlgebraicCombinatorics.Det.sumMatrix x y).det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_sumMatrix_eq_zero x y hn

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_transpose_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K) :
-- imply
  A.transpose.det = A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_transpose' A

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_upper_triangular_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (hA : ∀ i j, j < i → A i j = 0) :
-- imply
  A.det = ∏ i, A i i := by
-- proof
  apply AlgebraicCombinatorics.Det.det_upperTriangular A hA

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_lower_triangular_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (hA : ∀ i j, i < j → A i j = 0) :
-- imply
  A.det = ∏ i, A i i := by
-- proof
  apply AlgebraicCombinatorics.Det.det_lowerTriangular A hA

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_diagonal_eq
  [CommRing K]
-- given
  (d : Fin n → K) :
-- imply
  (Matrix.diagonal d).det = ∏ i, d i := by
-- proof
  apply AlgebraicCombinatorics.Det.det_diagonal' d

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_swap_rows_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (i j : Fin n)
  (hij : i ≠ j) :
-- imply
  (Matrix.of (A ∘ Equiv.swap i j)).det = -A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_swap_rows A i j hij

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_zero_row_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (i : Fin n)
  (hi : ∀ j, A i j = 0) :
-- imply
  A.det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_zero_row A i hi

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_eq_rows_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (i j : Fin n)
  (hij : i ≠ j)
  (hrows : A i = A j) :
-- imply
  A.det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_eq_rows A i j hij hrows

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_scale_row_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (i : Fin n)
  (c : K) :
-- imply
  (A.updateRow i (c • A i)).det = c * A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_scale_row A i c

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_add_row_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (i j : Fin n)
  (hij : i ≠ j) :
-- imply
  (A.updateRow i (A i + A j)).det = A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_add_row A i j hij

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_add_smul_row_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (i j : Fin n)
  (hij : i ≠ j)
  (c : K) :
-- imply
  (A.updateRow i (A i + c • A j)).det = A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_add_smul_row A i j hij c

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_row_add_eq
  [CommRing K]
-- given
  (A B C : Matrix (Fin n) (Fin n) K)
  (k : Fin n)
  (hk : C k = A k + B k)
  (hother : ∀ i, i ≠ k → C i = A i ∧ A i = B i) :
-- imply
  C.det = A.det + B.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_row_add A B C k hk hother

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_swap_cols_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (i j : Fin n)
  (hij : i ≠ j) :
-- imply
  (A.submatrix id (Equiv.swap i j)).det = -A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_swap_cols A i j hij

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_zero_col_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (j : Fin n)
  (hj : ∀ i, A i j = 0) :
-- imply
  A.det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_zero_col A j hj

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_eq_cols_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (i j : Fin n)
  (hij : i ≠ j)
  (hcols : ∀ k, A k i = A k j) :
-- imply
  A.det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_eq_cols A i j hij hcols

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_scale_col_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (j : Fin n)
  (c : K) :
-- imply
  (Matrix.of fun i k => if k = j then c * A i k else A i k).det = c * A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_scale_col A j c

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_add_col_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (i j : Fin n)
  (hij : i ≠ j) :
-- imply
  (A.updateCol i (fun k => A k i + A k j)).det = A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_add_col A i j hij

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_add_smul_col_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (i j : Fin n)
  (hij : i ≠ j)
  (c : K) :
-- imply
  (A.updateCol i (fun k => A k i + c * A k j)).det = A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_add_smul_col A i j hij c

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_col_add_eq
  [CommRing K]
-- given
  (A B C : Matrix (Fin n) (Fin n) K)
  (k : Fin n)
  (hk : ∀ i, C i k = A i k + B i k)
  (hother : ∀ i j, j ≠ k → C i j = A i j ∧ A i j = B i j) :
-- imply
  C.det = A.det + B.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_col_add A B C k hk hother

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_permute_rows_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (τ : Equiv.Perm (Fin n)) :
-- imply
  (A.submatrix τ id).det = Equiv.Perm.sign τ * A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_permute_rows A τ

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_permute_cols_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (τ : Equiv.Perm (Fin n)) :
-- imply
  (A.submatrix id τ).det = Equiv.Perm.sign τ * A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_permute_cols A τ

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_mul_eq
  [CommRing K]
-- given
  (A B : Matrix (Fin n) (Fin n) K) :
-- imply
  (A * B).det = A.det * B.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_mul' A B

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_scale_rows_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (d : Fin n → K) :
-- imply
  (Matrix.of fun i j => d i * A i j).det = (∏ i, d i) * A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_scale_rows A d

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_scale_cols_eq
  [CommRing K]
-- given
  (A : Matrix (Fin n) (Fin n) K)
  (d : Fin n → K) :
-- imply
  (Matrix.of fun i j => d j * A i j).det = (∏ j, d j) * A.det := by
-- proof
  apply AlgebraicCombinatorics.Det.det_scale_cols A d

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_outer_product_eq_zero'_eq
  [CommRing K]
-- given
  (hn : 2 ≤ n)
  (x y : Fin n → K) :
-- imply
  (AlgebraicCombinatorics.Det.outerProductMatrix x y).det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_outerProduct_eq_zero' x y hn

/--
[DeterminantsBasic](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/DeterminantsBasic.lean)
-/
@[path]
private lemma det_sum_matrix_eq_zero'_eq
  [CommRing K]
-- given
  (hn : 3 ≤ n)
  (x y : Fin n → K) :
-- imply
  (AlgebraicCombinatorics.Det.sumMatrix x y).det = 0 := by
-- proof
  apply AlgebraicCombinatorics.Det.det_sumMatrix_eq_zero' x y hn


-- created on 2026-10-11
