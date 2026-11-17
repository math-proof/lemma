/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/ExteriorAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.LinearCombination
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.Real.Basic

@[expose] public section

open Matrix Finset Module

set_option autoImplicit false


namespace ExteriorAlgebra

variable {R : Type*} [CommRing R] {n : ℕ}

def wedge (v w : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  fun i j => v i * w j - w i * v j

def antisymmMatrices (n : ℕ) (R : Type*) [CommRing R] :
    Submodule R (Matrix (Fin n) (Fin n) R) where
  carrier := {M | Mᵀ = -M}
  add_mem' {a b} (ha : aᵀ = -a) (hb : bᵀ = -b) := by
    show (a + b)ᵀ = -(a + b)
    rw [transpose_add, ha, hb, neg_add]
  zero_mem' := by simp
  smul_mem' r a (ha : aᵀ = -a) := by
    show (r • a)ᵀ = -(r • a)
    rw [transpose_smul, ha, smul_neg]

end ExteriorAlgebra
