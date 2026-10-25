/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/SOActionLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant


namespace SOAction

section DetIsometry

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
         [FiniteDimensional k V]

/-- The special isometry group $\mathrm{SO}(B)$: isometries of $B$ with determinant 1. -/
def SpecialIsometryGroup (B : LinearMap.BilinForm k V) : Set (V ≃ₗ[k] V) :=
  { g | (∀ v w, B (g v) (g w) = B v w) ∧ (g : V →ₗ[k] V).det = 1 }

end DetIsometry
end SOAction
