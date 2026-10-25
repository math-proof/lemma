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
import Abbrev.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Convert a linear equivalence `V ≃ₗ[k] V` to an element of the general linear
group `GLV k V`. -/
noncomputable def linearEquivToGLV (e : V ≃ₗ[k] V) : GLV k V :=
  ⟨e.toLinearMap, e.symm.toLinearMap,
   by ext x; simp,
   by ext x; simp⟩

end GeometricAlgebra
