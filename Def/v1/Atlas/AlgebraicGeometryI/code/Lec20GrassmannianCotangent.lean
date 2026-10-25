/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20GrassmannianCotangent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec20GrassmannianTangent.Part3
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.Lec20GrassmannianTangent
open Module


noncomputable section

universe u v

section Proposition37Cotangent

variable (F : Type u) [Field F]

variable (W : Type v) [AddCommGroup W] [Module F W]

/-- The trace pairing on the Grassmannian: a `k`-bilinear pairing
`T_V Gr × T^*_V Gr → F`, sending `(φ, ψ) ↦ tr(ψ ∘ φ)`. -/
def grassmannianTracePairing (kk : ℕ) (V : Module.Grassmannian F W kk)
    [FiniteDimensional F V.toSubmodule] :
    (grassmannianTangentSpace F W kk V) →ₗ[F]
    (grassmannianCotangentSpace F W kk V) →ₗ[F] F where
  toFun φ := {
    toFun := fun ψ => LinearMap.trace F V.toSubmodule (ψ.comp φ)
    map_add' := by intro ψ₁ ψ₂; simp [LinearMap.add_comp, map_add]
    map_smul' := by intro c ψ; simp [LinearMap.smul_comp, map_smul]
  }
  map_add' := by intro φ₁ φ₂; ext ψ; simp [LinearMap.comp_add, map_add]
  map_smul' := by intro c φ; ext ψ; simp [LinearMap.comp_smul, map_smul]

/-- The natural map `T^*_V Gr → (T_V Gr)*` induced by the trace pairing. -/
def cotangentToDualTangent (kk : ℕ) (V : Module.Grassmannian F W kk)
    [FiniteDimensional F V.toSubmodule] :
    (grassmannianCotangentSpace F W kk V) →ₗ[F]
    Module.Dual F (grassmannianTangentSpace F W kk V) where
  toFun ψ := {
    toFun := fun φ => LinearMap.trace F V.toSubmodule (ψ.comp φ)
    map_add' := by intro φ₁ φ₂; simp [LinearMap.comp_add, map_add]
    map_smul' := by intro c φ; simp [LinearMap.comp_smul, map_smul]
  }
  map_add' := by intro ψ₁ ψ₂; ext φ; simp [LinearMap.add_comp, map_add]
  map_smul' := by intro c ψ; ext φ; simp [LinearMap.smul_comp, map_smul]

end Proposition37Cotangent
end
