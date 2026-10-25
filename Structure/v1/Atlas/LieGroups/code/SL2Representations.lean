/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.LieGroups.code.SL2Basics.Part4
import Lemma.Nat.basisHC.eq.SMul
import Lemma.Complex.In_WeightSpace.is.H.eq.SMul
import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.KTypeDecomposition.Part3
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Theorem.v1.Atlas.LieGroups.code.SL2Representations
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

open Complex Module

structure SL2IrredGKModule.Realization
    (μ : SL2IrredGKModule)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)) where
  W : Type*
  [instAddCommGroup : AddCommGroup W]
  [instModule : Module ℂ W]
  [instLieRingModule : LieRingModule 𝔤 W]
  [instLieModule : LieModule ℂ 𝔤 W]
  gkmod : GKModule 𝔤 K 𝔨 Ad W
  casimirScalar : ℂ
  casimir_eq : casimirScalar = μ.casimirEigenvalue

end
