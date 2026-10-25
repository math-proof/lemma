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
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics


namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The underlying linear map of `linearEquivToGLV e` is `e.toLinearMap`. -/
@[simp] lemma linearEquivToGLV_val (e : V ≃ₗ[k] V) :
    (↑(linearEquivToGLV e) : V →ₗ[k] V) = e.toLinearMap := rfl

end GeometricAlgebra
