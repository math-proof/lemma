/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Group
public import Def.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics

public section

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The underlying linear map of `linearEquivToGLV e` is `e.toLinearMap`. -/
@[simp] lemma linearEquivToGLV_val (e : V ≃ₗ[k] V) :
    (↑(linearEquivToGLV e) : V →ₗ[k] V) = e.toLinearMap := rfl

end GeometricAlgebra
