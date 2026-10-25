/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittCancellationDirectSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.RelClasses
set_option maxHeartbeats 2000000


namespace Garrett

variable {k : Type*} [Field k] [NeZero (2 : k)]


/-- `φ : V₁ ≃ₗ V₂` is an isometry of formed spaces with respect to `B₁` and `B₂`
if it preserves the bilinear forms. -/
def IsFormedSpaceIso
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (φ : V₁ ≃ₗ[k] V₂) : Prop :=
  ∀ v w : V₁, B₂ (φ v) (φ w) = B₁ v w

/-- Orthogonal direct sum of two bilinear forms `B_U` on `U` and `B_W` on `W`. -/
def orthogonalSumForm
    {U W : Type*} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    (B_U : LinearMap.BilinForm k U) (B_W : LinearMap.BilinForm k W) :
    LinearMap.BilinForm k (U × W) :=
  LinearMap.mk₂ k
    (fun x y => B_U x.1 y.1 + B_W x.2 y.2)
    (fun x₁ x₂ y => by simp [map_add]; ring)
    (fun c x y => by simp [map_smul]; ring)
    (fun x y₁ y₂ => by simp [map_add]; ring)
    (fun c x y => by simp [map_smul]; ring)

end Garrett
