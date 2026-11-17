/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ContinuousRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Topology.Sequences
public import Structure.v1.Atlas.LieGroups.code.ContinuousRep.Part3

@[expose] public section

noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]

def RepEquiv.toRepHom
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    {π₁ : ContinuousRep G V} {π₂ : ContinuousRep G W}
    (e : RepEquiv π₁ π₂) : RepHom π₁ π₂ where
  toContinuousLinearMap := e.toContinuousLinearEquiv
  intertwines := e.intertwines

end ContinuousRep
end
