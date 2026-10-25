/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TranslationFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.FGUeaIotaRange
import Lemma.Int.All_Eq_0.of.EqCompositionLengthO_0.IsCategoryO
import Lemma.Int.IsCategoryOA.of.IsCategoryOB
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
import Def.v1.Atlas.LieGroups.code.BGGReciprocity.Part3
import Structure.v1.Atlas.LieGroups.code.TensorO
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Semisimple.Basic
import Theorem.v1.Atlas.LieGroups.code.TranslationFunctors.Part2


noncomputable section

open scoped TensorProduct

universe uM

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable (Δ : TriangularDecomposition R 𝔤)

variable (rd : PositiveRootData Δ)

variable (wg : WeylGroupData Δ)

local notation "𝔥*" => (Δ.𝔥 →ₗ[R] R)

attribute [instance] TranslationFunctorData.V_addCommGroup
  TranslationFunctorData.V_module TranslationFunctorData.V_lieRingModule
  TranslationFunctorData.V_lieModule TranslationFunctorData.V_finiteDim
  TranslationFunctorData.V_irreducible

attribute [instance] TranslationFunctorData.ApplyResult.instAddCommGroup
  TranslationFunctorData.ApplyResult.instModule
  TranslationFunctorData.ApplyResult.instLieRingModule
  TranslationFunctorData.ApplyResult.instLieModule

noncomputable def TranslationFunctorData.applyToModule
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F : TranslationFunctorData Δ rd wg)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    F.ApplyResult Δ rd wg M :=
  let act := ueaActionFromLieModule (R := R) (𝔤 := 𝔤) (F.V ⊗[R] M)
  let hcompat := ueaActionFromLieModule_compat (R := R) (𝔤 := 𝔤) (F.V ⊗[R] M)
  let χ := evalHC Δ wg F.mu
  let S := charEigenspaceLie act χ hcompat
  { carrier := ↥S
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instLieRingModule := inferInstance
    instLieModule := inferInstance
    hasInfChar :=
      { ueaAction := restrictedUEAAction act χ hcompat
        compat := restrictedUEAAction_compat act χ hcompat
        center_acts_by_scalar := restrictedUEA_center_acts act χ hcompat } }

end
