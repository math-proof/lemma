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
import Inductive.v1.Atlas.LieGroups.code.SL2Representations
attribute [local instance 100] LieRing.ofAssociativeRing

-- Mathlib keeps LieRing.ofAssociativeRing as a local instance only


noncomputable section

open Complex Module

namespace SL2IrredGKModule

def kTypes : SL2IrredGKModule → Set ℤ
  | finiteDim n => {m : ℤ | m % 2 = (n : ℤ) % 2 ∧ m.natAbs ≤ n}
  | principalSeries _ ε => {m : ℤ | (m : ZMod 2) = ε}
  | discreteSeriesPlus n _ => {m : ℤ | m ≥ (n : ℤ) ∧ m % 2 = (n : ℤ) % 2}
  | discreteSeriesMinus n _ => {m : ℤ | m ≤ -(n : ℤ) ∧ m % 2 = (n : ℤ) % 2}
  | limitDiscretePlus => {m : ℤ | m ≥ 1 ∧ m % 2 = 1}
  | limitDiscreteMinus => {m : ℤ | m ≤ -1 ∧ m % 2 = 1}

def casimirEigenvalue : SL2IrredGKModule → ℂ
  | finiteDim n => (n : ℂ) * ((n : ℂ) + 2)
  | principalSeries ν _ => 1 - ν ^ 2
  | discreteSeriesPlus n _ => (n : ℂ) * ((n : ℂ) - 2)
  | discreteSeriesMinus n _ => (n : ℂ) * ((n : ℂ) - 2)
  | limitDiscretePlus => -1
  | limitDiscreteMinus => -1

end SL2IrredGKModule

def GKModule.IsIsomorphicGK
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (M : GKModule 𝔤 K 𝔨 Ad V) (N : GKModule 𝔤 K 𝔨 Ad W) : Prop :=
  ∃ (φ : GKModuleHom M N), Function.Bijective φ.toLinearMap

end
