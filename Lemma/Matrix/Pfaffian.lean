import Mathlib
import sympy.Basic
import sympy.matrices.Pfaffian


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
