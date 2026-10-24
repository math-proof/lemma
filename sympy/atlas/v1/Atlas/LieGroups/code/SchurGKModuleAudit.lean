/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SchurGKModuleAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.Globalization
import Lemma.Submodule.Any_And_Le_Aleph0.of.IsIrreducibleGKModule
import Lemma.Int.Mul
import sympy.atlas.v1.Atlas.LieGroups.code.UnivEnvelopingAction

open UnivEnvelopingAction

noncomputable section


example {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) :
    ∀ (k : K) (X : 𝔤) (v : V), M.σ k (⁅X, v⁆) = ⁅Ad k X, M.σ k v⁆ :=
  M.equivariance


example {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule) :
    ∀ (W : Submodule ℂ V), M.IsSubmodule W → W = ⊥ ∨ W = ⊤ :=
  hirr


example (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    CenterUEA R L = Subalgebra.center R (UniversalEnvelopingAlgebra R L) :=
  rfl


example (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L]
    (χ : InfinitesimalCharacter R L) :
    CenterUEA R L →ₐ[R] R :=
  χ.toAlgHom


#check @center_acts_by_scalar


#check @schur_gkmodule


#check @schur_scalar_finiteDim


#check @schur_scalar_topological

end
