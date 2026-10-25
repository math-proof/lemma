/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModuleApplications.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible
import Class.v1.Atlas.LieGroups.code.DModuleApplications


noncomputable section

attribute [instance] SmoothVarietyWithGroupAction.grpK

attribute [instance] SmoothVarietyWithGroupAction.topK

attribute [instance] SmoothVarietyWithGroupAction.connK

attribute [instance] SmoothVarietyWithGroupAction.actKX

attribute [instance] SmoothVarietyWithGroupAction.ringDX

attribute [instance] SmoothVarietyWithGroupAction.algebraDX

attribute [instance] SmoothVarietyWithGroupAction.actKDX

attribute [instance] OrbitRepPair.addCommGroupV

attribute [instance] OrbitRepPair.moduleV

attribute [instance] OrbitRepPair.compGrpGroup

attribute [instance] IrredKEquivDModule.addCommGroup

attribute [instance] IrredKEquivDModule.moduleC

attribute [instance] IrredKEquivDModule.moduleDX

attribute [instance] IrredKEquivDModule.mulActionK

attribute [instance] HarishChandraData.grpG

attribute [instance] HarishChandraData.grpK

attribute [instance] HarishChandraData.lieRing𝔤

attribute [instance] HarishChandraData.lieAlgebra𝔤

attribute [instance] HarishChandraData.actK𝓕

attribute [instance] HarishChandraData.grpW

attribute [instance] HarishChandraData.fintypeW

attribute [instance] HarishChandraData.commRingZ

attribute [instance] HarishChandraData.algebraZ

attribute [instance] HarishChandraData.dotActionW

structure HCGKModule (D : HarishChandraData) where
  carrier : Type*
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  [lieRingModule : LieRingModule D.𝔤 carrier]
  [lieModule : LieModule ℂ D.𝔤 carrier]
  [mulAction : MulAction D.K carrier]
  χ : D.Z_Ug →ₐ[ℂ] ℂ

end
