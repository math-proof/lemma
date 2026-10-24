/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GrassmannianTangent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Prod

noncomputable section

open Module (finrank)

namespace Grassmannian

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

/-- Grassmannian chart at a point `V` with chosen complement `V'`: a linear map `V → V'` is sent
to its graph, viewed as a subspace of `W` via the splitting `W ≃ V × V'`. -/
def chart (V V' : Submodule F W) (hc : IsCompl V V')
    (φ : V →ₗ[F] V') : Submodule F W :=
  (LinearMap.graph φ).map (Submodule.prodEquivOfIsCompl V V' hc).toLinearMap

/-- Tangent-space identification at `V` (Prop 37, Lec 20): `Hom(V, V') ≃ Hom(V, W / V)`. -/
def tangentSpaceIso (V V' : Submodule F W) (hc : IsCompl V V') :
    (V →ₗ[F] V') ≃ₗ[F] (V →ₗ[F] (W ⧸ V)) :=
  LinearEquiv.arrowCongr (LinearEquiv.refl F V)
    (Submodule.quotientEquivOfIsCompl V V' hc).symm

/-- Cotangent-space identification at `V`: `Hom(V', V) ≃ Hom(W / V, V)` (dual of `tangentSpaceIso`). -/
def cotangentSpaceIso (V V' : Submodule F W) (hc : IsCompl V V') :
    (V' →ₗ[F] V) ≃ₗ[F] ((W ⧸ V) →ₗ[F] V) :=
  LinearEquiv.arrowCongr (Submodule.quotientEquivOfIsCompl V V' hc).symm
    (LinearEquiv.refl F V)

/-- Comparison isomorphism between tangent-space models for two different complements `V'₁, V'₂`. -/
def complementChangeIso
    (V V'₁ V'₂ : Submodule F W) (h₁ : IsCompl V V'₁) (h₂ : IsCompl V V'₂) :
    (V →ₗ[F] V'₁) ≃ₗ[F] (V →ₗ[F] V'₂) :=
  (tangentSpaceIso V V'₁ h₁).trans (tangentSpaceIso V V'₂ h₂).symm

/-- The `n`-th graded piece `I^n / I^{n+1}` of the associated graded of `I`. -/
abbrev associatedGradedComponent (R : Type*) [CommRing R] (I : Ideal R) (n : ℕ) :=
  (I ^ n : Submodule R R) ⧸
    Submodule.comap (I ^ n).subtype ((I ^ (n + 1) : Ideal R).restrictScalars R)

/-- The canonical map `I^n → I^n / I^{n+1}` projecting onto the `n`-th graded piece. -/
def associatedGradedComponent.mk {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    (I ^ n : Submodule R R) →ₗ[R] associatedGradedComponent R I n :=
  Submodule.mkQ _
