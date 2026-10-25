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
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part3


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

namespace Flag

/-- The image of a submodule under the product of two `GL` elements equals the
iterated image: `W.map (a * b) = (W.map b).map a`. -/
theorem submodule_map_mul_eq (a b : GLV k V) (W : Submodule k V) :
    W.map (↑(a * b) : V →ₗ[k] V) = (W.map (↑b : V →ₗ[k] V)).map (↑a : V →ₗ[k] V) := by
  ext x; simp only [Submodule.mem_map, Units.val_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨(b : V →ₗ[k] V) y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩

end Flag
end GeometricAlgebra
