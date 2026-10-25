/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CoordinateExamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Block
import Abbrev.v1.Atlas.Buildings.code.GeometricAlgebra.CoordinateExamples
open Matrix


namespace CoordinateExamples

/-- A matrix `g` is an invertible isometry of the bilinear form `F` when it is
invertible (its determinant is a unit) and form-preserving (`gᵀ F g = F`). -/
def IsInvertibleIsometry {m : ℕ} {k : Type*} [CommRing k]
    (F : Matrix (Fin m) (Fin m) k) (g : Matrix (Fin m) (Fin m) k) : Prop :=
  IsUnit g.det ∧ g.transpose * F * g = F

/-- The matrix isometry group of a bilinear form matrix `J`: the subgroup of
`GL ι k` consisting of matrices `g` satisfying `gᵀ J g = J`. -/
def MatrixIsometryGroup {ι : Type*} [DecidableEq ι] [Fintype ι]
    {k : Type*} [CommRing k] (J : Matrix ι ι k) : Subgroup (GL ι k) where
  carrier := {g | g.val.transpose * J * g.val = J}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    show (a * b).val.transpose * J * (a * b).val = J
    simp only [Units.val_mul, Matrix.transpose_mul]
    calc b.val.transpose * a.val.transpose * J * (a.val * b.val)
        = b.val.transpose * (a.val.transpose * J * a.val) * b.val := by
          simp [Matrix.mul_assoc]
      _ = b.val.transpose * J * b.val := by rw [ha]
      _ = J := hb
  one_mem' := by simp [Set.mem_setOf_eq, Units.val_one, Matrix.transpose_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    have h1 : a.val * a⁻¹.val = 1 := a.val_inv
    have h3 : a⁻¹.val.transpose * a.val.transpose = 1 := by
      rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc a⁻¹.val.transpose * J * a⁻¹.val
        = a⁻¹.val.transpose * (a.val.transpose * J * a.val) * a⁻¹.val := by rw [ha]
      _ = (a⁻¹.val.transpose * a.val.transpose) * J * (a.val * a⁻¹.val) := by
          simp [Matrix.mul_assoc]
      _ = 1 * J * 1 := by rw [h3, h1]
      _ = J := by simp

/-- The symplectic group `Sp(2n, k)`: the matrix isometry group of the standard
symplectic form on `kⁿ ⊕ kⁿ`. -/
noncomputable def Sp (n : ℕ) (k : Type*) [CommRing k] :
    Subgroup (GL (Fin n ⊕ Fin n) k) :=
  MatrixIsometryGroup (symplecticFormMatrix n k)

/-- The split-orthogonal group `O(n, n; k)`: the matrix isometry group of the
standard hyperbolic symmetric form on `kⁿ ⊕ kⁿ`. -/
def OrthoSplit (n : ℕ) (k : Type*) [CommRing k] :
    Subgroup (GL (Fin n ⊕ Fin n) k) :=
  MatrixIsometryGroup (splitOrthogonalFormMatrix n k)

/-- The orthogonal group `O(p, q; k)` of signature `(p, q)`: the matrix isometry
group of the standard `(p, q)`-form on `kᵖ ⊕ kᵠ`. -/
noncomputable def OrthogonalPQ (p q : ℕ) (k : Type*) [CommRing k] :
    Subgroup (GL (Fin p ⊕ Fin q) k) :=
  MatrixIsometryGroup (orthogonalFormMatrix p q k)

end CoordinateExamples
