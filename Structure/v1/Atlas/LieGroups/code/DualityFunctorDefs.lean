/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DualityFunctorDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CompositionSeries
import Lemma.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma


noncomputable section

universe uCatO

structure CartanInvolution
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) where
  τ : 𝔤 →ₗ[R] 𝔤
  involution : τ ∘ₗ τ = LinearMap.id
  negate_cartan : ∀ h : Δ.𝔥, τ (h : 𝔤) = -(h : 𝔤)
  anti_hom : ∀ (X Y : 𝔤), τ ⁅X, Y⁆ = ⁅τ Y, τ X⁆

structure DualInO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hX : IsCategoryO Δ rd X) where
  Xdual : Type uCatO
  [instAddCommGroup : AddCommGroup Xdual]
  [instModule : Module R Xdual]
  [instLieRingModule : LieRingModule 𝔤 Xdual]
  [instLieModule : LieModule R 𝔤 Xdual]
  isCategoryO : IsCategoryO Δ rd Xdual

end
