/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TranslationFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
public import Lemma.Int.WeightLE.of.BruhatLE
public import Lemma.Int.FGUeaIotaRange
public import Lemma.Int.All_Eq_0.of.EqCompositionLengthO_0.IsCategoryO
public import Theorem.Int.IsCategoryOA.of.IsCategoryOB
public import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
public import Def.v1.Atlas.LieGroups.code.BGGReciprocity.Part3
public import Structure.v1.Atlas.LieGroups.code.TensorO
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Notation.v1.Atlas.LieGroups.code.TranslationFunctors


public noncomputable section

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
