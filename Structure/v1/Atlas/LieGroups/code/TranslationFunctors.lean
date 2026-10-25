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
import Notation.v1.Atlas.LieGroups.code.TranslationFunctors


noncomputable section

open scoped TensorProduct

universe uM

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable (Δ : TriangularDecomposition R 𝔤)

variable (rd : PositiveRootData Δ)

variable (wg : WeylGroupData Δ)

local notation "𝔥*" => (Δ.𝔥 →ₗ[R] R)

structure TranslationFunctorData where
  lam : 𝔥*
  mu : 𝔥*
  V : Type*
  [V_addCommGroup : AddCommGroup V]
  [V_module : Module R V]
  [V_lieRingModule : LieRingModule 𝔤 V]
  [V_lieModule : LieModule R 𝔤 V]
  [V_finiteDim : Module.Finite R V]
  [V_irreducible : IsSimpleModule R V]
  lam_dominant : IsDominantWeightLE rd wg lam
  mu_dominant : IsDominantWeightLE rd wg mu
  extremal_weight : mu - lam ∈ weights Δ V

attribute [instance] TranslationFunctorData.V_addCommGroup
  TranslationFunctorData.V_module TranslationFunctorData.V_lieRingModule
  TranslationFunctorData.V_lieModule TranslationFunctorData.V_finiteDim
  TranslationFunctorData.V_irreducible

structure TranslationFunctorData.ApplyResult
    (F : TranslationFunctorData Δ rd wg)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  carrier : Type*
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  [instLieRingModule : LieRingModule 𝔤 carrier]
  [instLieModule : LieModule R 𝔤 carrier]
  hasInfChar : HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) carrier (evalHC Δ wg F.mu)

end
