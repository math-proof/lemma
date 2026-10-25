/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ContinuousRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Sequences
import Def.v1.Atlas.LieGroups.code.ContinuousRep.Part2


noncomputable section

open scoped ComplexOrder

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

variable {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]

structure RepHom
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) where
  toContinuousLinearMap : V →L[ℂ] W
  intertwines : ∀ g : G,
    toContinuousLinearMap.comp (π₁.toMonoidHom g) =
    (π₂.toMonoidHom g).comp toContinuousLinearMap

structure RepEquiv
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) where
  toContinuousLinearEquiv : V ≃L[ℂ] W
  intertwines : ∀ g : G,
    (toContinuousLinearEquiv : V →L[ℂ] W).comp (π₁.toMonoidHom g) =
    (π₂.toMonoidHom g).comp (toContinuousLinearEquiv : V →L[ℂ] W)

end ContinuousRep
end
