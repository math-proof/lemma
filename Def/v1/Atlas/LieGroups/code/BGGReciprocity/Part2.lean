/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGReciprocity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CompositionSeries
import Lemma.Int.StandardFiltrationMultiplicity.eq.DimHomProjectiveContragredientVerma
import Def.v1.Atlas.LieGroups.code.DualityFunctorDefs
import Theorem.v1.Atlas.LieGroups.code.BGGReciprocity


noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

noncomputable def lieModuleHomToUEALinearMap_gen
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {N : Type*} [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    letI := instModuleUEASubalg Δ.𝔫_neg N
    M →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] N := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  letI := instModuleUEASubalg Δ.𝔫_neg N
  exact {
    toFun := f
    map_add' := f.toLinearMap.map_add
    map_smul' := fun r m => lieModuleHom_ueaSubalg_compat_gen f r m

  }


end
