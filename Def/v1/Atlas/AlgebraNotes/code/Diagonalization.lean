/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Diagonalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

namespace Diagonalization

open Module Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def IsDiagonalizable {n : Type*} [Fintype n] [DecidableEq n]
    {F : Type*} [Field F] (A : Matrix n n F) : Prop :=
  ∃ (P : Matrix n n F) (_ : Invertible P) (d : n → F), P⁻¹ * A * P = diagonal d

end Diagonalization
