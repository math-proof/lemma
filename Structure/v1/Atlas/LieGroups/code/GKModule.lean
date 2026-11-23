/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GKModule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part3
public import Theorem.Complex.IsStronglyContinuousToMonoidHom
public import Theorem.Complex.IsKFinite0
public import Def.v1.Atlas.LieGroups.code.KFinite.Part3
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Def.v1.Atlas.LieGroups.code.GKModule


public noncomputable section

structure GKModule
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V] where
  σ : Representation ℂ K V
  locallyFinite : σ.IsLocallyFinite
  diffσ : 𝔨 →ₗ[ℂ] (V →ₗ[ℂ] V)
  diff_eq_lie : ∀ (X : 𝔨) (v : V), diffσ X v = ⁅(X : 𝔤), v⁆
  equivariance : ∀ (k : K) (X : 𝔤) (v : V),
    σ k (⁅X, v⁆) = ⁅Ad k X, σ k v⁆

structure GKModuleHom
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (M : GKModule 𝔤 K 𝔨 Ad V) (N : GKModule 𝔤 K 𝔨 Ad W) where
  toLinearMap : V →ₗ[ℂ] W
  lie_comm : ∀ (X : 𝔤) (v : V), toLinearMap ⁅X, v⁆ = ⁅X, toLinearMap v⁆
  group_comm : ∀ (k : K) (v : V), toLinearMap (M.σ k v) = N.σ k (toLinearMap v)

namespace GKModule

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]

variable {K : Type*} [Group K]

variable {𝔨 : LieSubalgebra ℂ 𝔤}

variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]

structure IsSubmodule (M : GKModule 𝔤 K 𝔨 Ad V) (W : Submodule ℂ V) : Prop where
  lie_invariant : ∀ (X : 𝔤) (w : V), w ∈ W → ⁅X, w⁆ ∈ W
  group_invariant : ∀ (k : K) (w : V), w ∈ W → M.σ k w ∈ W

end GKModule
end
