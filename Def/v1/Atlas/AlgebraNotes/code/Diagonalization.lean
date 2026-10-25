/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Diagonalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse


namespace Diagonalization

open Module Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def IsDiagonalizable {n : Type*} [Fintype n] [DecidableEq n]
    {F : Type*} [Field F] (A : Matrix n n F) : Prop :=
  ∃ (P : Matrix n n F) (_ : Invertible P) (d : n → F), P⁻¹ * A * P = diagonal d

end Diagonalization
