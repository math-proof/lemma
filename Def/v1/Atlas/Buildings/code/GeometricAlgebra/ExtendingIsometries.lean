/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/ExtendingIsometries.lean -/

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


namespace Garrett

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- A submodule `U` is totally isotropic for `B` when `B` vanishes on all pairs of
elements of `U`. -/
def IsTotallyIsotropic (B : LinearMap.BilinForm k V) (U : Submodule k V) : Prop :=
  ∀ u₁ ∈ U, ∀ u₂ ∈ U, B u₁ u₂ = 0

/-- A linear isomorphism `φ : U ≃ₗ W` between two submodules is a subspace
isometry for `B` when it preserves the values of `B`. -/
def IsSubspaceIsometry (B : LinearMap.BilinForm k V) (U W : Submodule k V)
    (φ : U ≃ₗ[k] W) : Prop :=
  ∀ u₁ u₂ : U, B (φ u₁ : V) (φ u₂ : V) = B (u₁ : V) (u₂ : V)


/-- Witt extension property for `B`: when `B` is nondegenerate, every subspace
isometry between two submodules extends to a global isometry of `V`. -/
def WittExtensionProp (B : LinearMap.BilinForm k V) : Prop :=
  LinearMap.BilinForm.orthogonal B ⊤ = ⊥ →
  ∀ (U W : Submodule k V) (φ : U ≃ₗ[k] W),
    IsSubspaceIsometry B U W φ →
    ∃ Φ : V ≃ₗ[k] V,
      (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧
      (∀ u : U, Φ (u : V) = (φ u : V))

/-- Witt cancellation property for `B`: when `B` is nondegenerate, every
isometry between two submodules induces an isometry between their orthogonal
complements. -/
def WittCancellationProp (B : LinearMap.BilinForm k V) : Prop :=
  LinearMap.BilinForm.orthogonal B ⊤ = ⊥ →
  ∀ (U₁ U₂ : Submodule k V) (φ : U₁ ≃ₗ[k] U₂),
    IsSubspaceIsometry B U₁ U₂ φ →
    ∃ ψ : (LinearMap.BilinForm.orthogonal B U₁) ≃ₗ[k]
           (LinearMap.BilinForm.orthogonal B U₂),
      IsSubspaceIsometry B
        (LinearMap.BilinForm.orthogonal B U₁)
        (LinearMap.BilinForm.orthogonal B U₂) ψ

end Garrett
