/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Group
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Convert an element of the general linear group `GLV k V` back to a linear
equivalence `V ≃ₗ[k] V`. -/
noncomputable def glvToLinearEquiv (g : GLV k V) : V ≃ₗ[k] V :=
  LinearEquiv.ofLinear (↑g : V →ₗ[k] V) (↑(g⁻¹) : V →ₗ[k] V)
    (by ext x; change (↑(g * g⁻¹) : V →ₗ[k] V) x = x; simp [mul_inv_cancel])
    (by ext x; change (↑(g⁻¹ * g) : V →ₗ[k] V) x = x; simp [inv_mul_cancel])

end GeometricAlgebra
