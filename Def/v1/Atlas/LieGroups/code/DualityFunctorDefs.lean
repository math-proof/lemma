/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DualityFunctorDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CompositionSeries
import Lemma.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
import Structure.v1.Atlas.LieGroups.code.DualityFunctorDefs


noncomputable section

universe uCatO

attribute [instance] DualInO.instAddCommGroup DualInO.instModule
  DualInO.instLieRingModule DualInO.instLieModule

def IsContragredientVerma
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (M : Type uCatO) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hM : IsCategoryO Δ rd M) : Prop :=
  ∃ (Mlam : Type uCatO) (_ : AddCommGroup Mlam) (_ : Module R Mlam)
    (_ : LieRingModule 𝔤 Mlam) (_ : LieModule R 𝔤 Mlam),
    Nonempty (IsVermaModule Δ Mlam lam) ∧ IsCategoryO Δ rd Mlam ∧
    (∃ (β : M →ₗ[R] Mlam →ₗ[R] R),
      (∀ (x : 𝔤) (m : M) (m' : Mlam), β (⁅x, m⁆) m' + β m ⁅x, m'⁆ = 0) ∧
      (∀ m : M, (∀ m' : Mlam, β m m' = 0) → m = 0) ∧
      (∀ m' : Mlam, (∀ m : M, β m m' = 0) → m' = 0))

end
