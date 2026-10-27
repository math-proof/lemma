import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.Pfaffian


section
-- ac-theorems

/-- Diagonal entries of a skew-symmetric matrix are zero (in characteristic ≠ 2). -/
lemma Matrix.IsSkewSymmetric.diag_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] [NoZeroDivisors R] [CharZero R]
    {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) (i : n) : A i i = 0 := by
  have h : A.transpose i i = (-A) i i := congrFun (congrFun hA i) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  -- h : A i i = -A i i
  -- This means 2 * A i i = 0
  have h2 : A i i = -A i i := h
  have h3 : A i i - (-A i i) = 0 := sub_eq_zero.mpr h2
  simp only [sub_neg_eq_add] at h3
  -- h3 : A i i + A i i = 0
  have h4 : (2 : R) * A i i = 0 := by rw [two_mul]; exact h3
  exact (mul_eq_zero.mp h4).resolve_left (by norm_num : (2 : R) ≠ 0)

/-- For a skew-symmetric matrix, A i j = -A j i. -/
lemma Matrix.IsSkewSymmetric.apply_neg {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) (i j : n) :
    A i j = -A j i := by
  have h : A.transpose j i = (-A) j i := congrFun (congrFun hA j) i
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  exact h

/-- Skew-symmetry is preserved under reindexing. -/
lemma Matrix.IsSkewSymmetric.reindex {n m : Type*} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] {R : Type*} [Ring R]
    {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) (e : n ≃ m) :
    Matrix.IsSkewSymmetric (A.reindex e e) := by
  unfold Matrix.IsSkewSymmetric at *
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.reindex_apply,
             Matrix.submatrix_apply]
  have h : A.transpose (e.symm i) (e.symm j) = (-A) (e.symm i) (e.symm j) :=
    congrFun (congrFun hA (e.symm i)) (e.symm j)
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  exact h

/-- Skew-symmetry is preserved under map when the map preserves negation. -/
lemma Matrix.IsSkewSymmetric.map {n : Type*} [Fintype n] [DecidableEq n]
    {R S : Type*} [Ring R] [Ring S]
    {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A)
    (f : R → S) (hf : ∀ x, f (-x) = -f x) :
    Matrix.IsSkewSymmetric (A.map f) := by
  unfold Matrix.IsSkewSymmetric at *
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.map_apply]
  have h : A.transpose i j = (-A) i j := congrFun (congrFun hA i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  rw [h, hf]

/-- Skew-symmetry is preserved under scalar multiplication. -/
lemma Matrix.IsSkewSymmetric.smul {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) (c : R) :
    Matrix.IsSkewSymmetric (c • A) := by
  unfold Matrix.IsSkewSymmetric at *
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  have h : A.transpose i j = (-A) i j := congrFun (congrFun hA i) j
  simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
  rw [h, mul_neg]

/-- The zero matrix is skew-symmetric. -/
lemma Matrix.IsSkewSymmetric.zero {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] : Matrix.IsSkewSymmetric (0 : Matrix n n R) := by
  unfold Matrix.IsSkewSymmetric
  simp only [Matrix.transpose_zero, neg_zero]

/-- The sum of skew-symmetric matrices is skew-symmetric. -/
lemma Matrix.IsSkewSymmetric.add {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] {A B : Matrix n n R}
    (hA : Matrix.IsSkewSymmetric A) (hB : Matrix.IsSkewSymmetric B) :
    Matrix.IsSkewSymmetric (A + B) := by
  unfold Matrix.IsSkewSymmetric at *
  simp only [Matrix.transpose_add, hA, hB, neg_add]

/-- The negation of a skew-symmetric matrix is skew-symmetric. -/
lemma Matrix.IsSkewSymmetric.neg {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) :
    Matrix.IsSkewSymmetric (-A) := by
  unfold Matrix.IsSkewSymmetric at *
  simp only [Matrix.transpose_neg, hA, neg_neg]

/-- The difference of two skew-symmetric matrices is skew-symmetric. -/
lemma Matrix.IsSkewSymmetric.sub {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [Ring R] {A B : Matrix n n R}
    (hA : Matrix.IsSkewSymmetric A) (hB : Matrix.IsSkewSymmetric B) :
    Matrix.IsSkewSymmetric (A - B) := by
  unfold Matrix.IsSkewSymmetric at *
  simp only [Matrix.transpose_sub, hA, hB, neg_sub, sub_neg_eq_add, neg_add_eq_sub]

/-- The determinant of an odd-dimensional skew-symmetric matrix is zero.
    This follows from det(A) = det(Aᵀ) = det(-A) = (-1)^n det(A) = -det(A),
    hence 2 det(A) = 0, so det(A) = 0 (in characteristic ≠ 2). -/
lemma Matrix.IsSkewSymmetric.det_eq_zero_of_odd {n : ℕ} {R : Type*}
    [CommRing R] [NoZeroDivisors R] [CharZero R]
    (A : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) R)
    (hA : Matrix.IsSkewSymmetric A) : A.det = 0 := by
  have h1 : A.det = A.transpose.det := (Matrix.det_transpose A).symm
  have h2 : A.transpose.det = (-A).det := congrArg Matrix.det hA
  have h3 : (-A).det = (-1 : R) ^ (2 * n + 1) * A.det := by
    rw [Matrix.det_neg]
    simp only [Fintype.card_fin]
  have h4 : (-1 : R) ^ (2 * n + 1) = -1 := by
    rw [pow_add, pow_mul]
    simp only [neg_one_sq, one_pow, pow_one, one_mul]
  rw [h4] at h3
  have h5 : A.det = -A.det := by
    calc A.det = A.transpose.det := h1
    _ = (-A).det := h2
    _ = -1 * A.det := h3
    _ = -A.det := by ring
  have h6 : A.det + A.det = 0 := by
    have : A.det - (-A.det) = 0 := sub_eq_zero.mpr h5
    simp only [sub_neg_eq_add] at this
    exact this
  have h7 : (2 : R) * A.det = 0 := by rw [two_mul]; exact h6
  exact (mul_eq_zero.mp h7).resolve_left (by norm_num : (2 : R) ≠ 0)
end


/--
[Pfaffian](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Extra/Pfaffian.lean)
-/
@[path]
private lemma matrix_is_skew_symmetric_diag_eq_zero_eq
  [Fintype n] [DecidableEq n] [Ring R] [NoZeroDivisors R] [CharZero R]
  {A : Matrix n n R}
-- given
  (hA : Matrix.IsSkewSymmetric A)
  (i : n) :
-- imply
  A i i = 0 := by
-- proof
  apply Matrix.IsSkewSymmetric.diag_eq_zero hA i

/--
[Pfaffian](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Extra/Pfaffian.lean)
-/
@[path]
private lemma matrix_is_skew_symmetric_apply_neg_eq
  [Fintype n] [DecidableEq n] [Ring R]
  {A : Matrix n n R}
-- given
  (hA : Matrix.IsSkewSymmetric A)
  (i j : n) :
-- imply
  A i j = -A j i := by
-- proof
  apply Matrix.IsSkewSymmetric.apply_neg hA i j

/--
[Pfaffian](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Extra/Pfaffian.lean)
-/
@[path]
private lemma matrix_is_skew_symmetric_reindex_is
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Ring R]
  {A : Matrix n n R}
-- given
  (hA : Matrix.IsSkewSymmetric A)
  (e : n ≃ m) :
-- imply
  Matrix.IsSkewSymmetric (A.reindex e e) := by
-- proof
  apply Matrix.IsSkewSymmetric.reindex hA e

/--
[Pfaffian](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Extra/Pfaffian.lean)
-/
@[path]
private lemma matrix_is_skew_symmetric_map_is
  [Fintype n] [DecidableEq n] [Ring R] [Ring S]
  {A : Matrix n n R}
-- given
  (f : R → S)
  (hA : Matrix.IsSkewSymmetric A)
  (hf : ∀ x, f (-x) = -f x) :
-- imply
  Matrix.IsSkewSymmetric (A.map f) := by
-- proof
  apply Matrix.IsSkewSymmetric.map hA f hf

/--
[Pfaffian](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Extra/Pfaffian.lean)
-/
@[path]
private lemma matrix_is_skew_symmetric_smul_is
  [Fintype n] [DecidableEq n] [Ring R]
  {A : Matrix n n R}
-- given
  (hA : Matrix.IsSkewSymmetric A)
  (c : R) :
-- imply
  Matrix.IsSkewSymmetric (c • A) := by
-- proof
  apply Matrix.IsSkewSymmetric.smul hA c

/--
[Pfaffian](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Extra/Pfaffian.lean)
-/
@[path]
private lemma matrix_is_skew_symmetric_zero_is
  [Fintype n] [DecidableEq n] [Ring R] :
-- imply
  Matrix.IsSkewSymmetric (0 : Matrix n n R) := by
-- proof
  apply Matrix.IsSkewSymmetric.zero

/--
[Pfaffian](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Extra/Pfaffian.lean)
-/
@[path]
private lemma matrix_is_skew_symmetric_add_is
  [Fintype n] [DecidableEq n] [Ring R]
  {A B : Matrix n n R}
-- given
  (hA : Matrix.IsSkewSymmetric A)
  (hB : Matrix.IsSkewSymmetric B) :
-- imply
  Matrix.IsSkewSymmetric (A + B) := by
-- proof
  apply Matrix.IsSkewSymmetric.add hA hB

/--
[Pfaffian](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Extra/Pfaffian.lean)
-/
@[path]
private lemma matrix_is_skew_symmetric_neg_is
  [Fintype n] [DecidableEq n] [Ring R]
  {A : Matrix n n R}
-- given
  (hA : Matrix.IsSkewSymmetric A) :
-- imply
  Matrix.IsSkewSymmetric (-A) := by
-- proof
  apply Matrix.IsSkewSymmetric.neg hA

/--
[Pfaffian](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Extra/Pfaffian.lean)
-/
@[path]
private lemma matrix_is_skew_symmetric_sub_is
  [Fintype n] [DecidableEq n] [Ring R]
  {A B : Matrix n n R}
-- given
  (hA : Matrix.IsSkewSymmetric A)
  (hB : Matrix.IsSkewSymmetric B) :
-- imply
  Matrix.IsSkewSymmetric (A - B) := by
-- proof
  apply Matrix.IsSkewSymmetric.sub hA hB

/--
[Pfaffian](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Extra/Pfaffian.lean)
-/
@[path]
private lemma matrix_is_skew_symmetric_det_eq_zero_of_odd_eq
  [CommRing R] [NoZeroDivisors R] [CharZero R]
-- given
  (A : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) R)
  (hA : Matrix.IsSkewSymmetric A) :
-- imply
  A.det = 0 := by
-- proof
  apply Matrix.IsSkewSymmetric.det_eq_zero_of_odd A hA


-- created on 2026-10-11
