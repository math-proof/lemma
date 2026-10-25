/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangentProp37.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Prod


noncomputable section

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

/-- Grassmannian chart at `V` with complement `V'`: sends `φ : V → V'` to its graph in `W`. -/
def grassmannianChart (V V' : Submodule F W) (hc : IsCompl V V')
    (φ : V →ₗ[F] V') : Submodule F W :=
  (LinearMap.graph φ).map (Submodule.prodEquivOfIsCompl V V' hc).toLinearMap

/-- Tangent-space isomorphism for the Grassmannian: `Hom(V, V') ≃ Hom(V, W / V)`. -/
def grassmannianTangentIso (V V' : Submodule F W) (hc : IsCompl V V') :
    (V →ₗ[F] V') ≃ₗ[F] (V →ₗ[F] (W ⧸ V)) :=
  LinearEquiv.arrowCongr (LinearEquiv.refl F V)
    (Submodule.quotientEquivOfIsCompl V V' hc).symm

/-- Cotangent-space isomorphism for the Grassmannian: `Hom(V', V) ≃ Hom(W / V, V)`. -/
def grassmannianCotangentIso (V V' : Submodule F W) (hc : IsCompl V V') :
    (V' →ₗ[F] V) ≃ₗ[F] ((W ⧸ V) →ₗ[F] V) :=
  LinearEquiv.arrowCongr (Submodule.quotientEquivOfIsCompl V V' hc).symm
    (LinearEquiv.refl F V)

/-- Comparison isomorphism between the tangent space at `V` computed via complement `V'₁` vs `V'₂`. -/
def grassmannianTangentIso_independence
    (V V'₁ V'₂ : Submodule F W) (h₁ : IsCompl V V'₁) (h₂ : IsCompl V V'₂) :
    (V →ₗ[F] V'₁) ≃ₗ[F] (V →ₗ[F] V'₂) :=
  (grassmannianTangentIso V V'₁ h₁).trans (grassmannianTangentIso V V'₂ h₂).symm

end
