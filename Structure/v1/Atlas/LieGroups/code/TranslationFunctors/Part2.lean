/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TranslationFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
public import Theorem.Int.WeightLE.of.BruhatLE
public import Theorem.Int.FGUeaIotaRange
public import Theorem.Int.All_Eq_0.of.EqCompositionLengthO_0.IsCategoryO
public import Theorem.Int.IsCategoryOA.of.IsCategoryOB
public import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
public import Def.v1.Atlas.LieGroups.code.BGGReciprocity.Part3
public import Structure.v1.Atlas.LieGroups.code.TensorO
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Def.v1.Atlas.LieGroups.code.TranslationFunctors.Part3


public noncomputable section

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

structure IsContragredientLieModule
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (W : Type*) [AddCommGroup W] [Module R W]
    [LieRingModule 𝔤 W] [LieModule R 𝔤 W] where
  pairing : V →ₗ[R] W →ₗ[R] R
  nondegenerate_left : ∀ v : V, (∀ w : W, pairing v w = 0) → v = 0
  nondegenerate_right : ∀ w : W, (∀ v : V, pairing v w = 0) → w = 0
  equivariant : ∀ (x : 𝔤) (v : V) (w : W),
    pairing (⁅x, v⁆) w + pairing v (⁅x, w⁆) = 0

end
