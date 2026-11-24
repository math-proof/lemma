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


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GKModule.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

def Representation.IsLocallyFinite {K V : Type*} [Group K]
    [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ K V) : Prop :=
  ∀ v : V, FiniteDimensional ℂ
    (Submodule.span ℂ (Set.range (fun k : K => (σ k) v)) : Submodule ℂ V)

end
