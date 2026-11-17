/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittCancellationDirectSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Order.RelClasses
public import Def.v1.Atlas.Buildings.code.GeometricAlgebra.WittCancellationDirectSum
set_option maxHeartbeats 2000000

public section

namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]


/-- Evaluation formula for the orthogonal direct sum bilinear form. -/
@[simp]
theorem orthogonalSumForm_apply
    {U W : Type*} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    (B_U : LinearMap.BilinForm k U) (B_W : LinearMap.BilinForm k W)
    (x y : U × W) :
    orthogonalSumForm B_U B_W x y = B_U x.1 y.1 + B_W x.2 y.2 := by
  simp [orthogonalSumForm, LinearMap.mk₂]

end Garrett
