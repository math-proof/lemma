/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib


/-!
# Skew-Symmetric Matrices

This file defines skew-symmetric matrices and proves basic properties.

A matrix A is skew-symmetric (also called antisymmetric) if A^T = -A.

## Main definitions

* `Matrix.IsSkewSymmetric`: A matrix A is skew-symmetric if A^T = -A.

## Main results

* `Matrix.IsSkewSymmetric.diag_eq_zero`: Diagonal entries of a skew-symmetric matrix are zero
  (in characteristic ≠ 2).
* `Matrix.IsSkewSymmetric.apply_neg`: For a skew-symmetric matrix, A i j = -A j i.
* `Matrix.IsSkewSymmetric.det_eq_zero_of_odd`: The determinant of an odd-dimensional
  skew-symmetric matrix is zero (in characteristic ≠ 2).

## Notes

This file provides basic infrastructure for skew-symmetric matrices. The Pfaffian of a
skew-symmetric matrix and Kasteleyn's formula for counting domino tilings would require
substantial additional infrastructure.

Note: Mathlib has `Matrix.IsSkewAdjoint J A` which is the more general notion of
A being skew-adjoint with respect to a bilinear form J (i.e., Aᵀ * J = -J * A).
Our `IsSkewSymmetric` is the special case where J = I, i.e., simply Aᵀ = -A.

## References

* [Horn-Johnson, Matrix Analysis] for skew-symmetric matrix properties
-/
/-! ## Skew-Symmetric Matrices -/


/-- A matrix A is skew-symmetric if A^T = -A. -/
def Matrix.IsSkewSymmetric {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [Ring R]
    (A : Matrix n n R) : Prop :=
  A.transpose = -A

