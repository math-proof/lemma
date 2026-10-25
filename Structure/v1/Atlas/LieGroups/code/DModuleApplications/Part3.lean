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
import Def.v1.Atlas.LieGroups.code.DModuleApplications.Part2


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

structure HarishChandraData where
  G : Type*
  [grpG : Group G]
  K : Type*
  [grpK : Group K]
  𝔤 : Type*
  [lieRing𝔤 : LieRing 𝔤]
  [lieAlgebra𝔤 : LieAlgebra ℂ 𝔤]
  𝓕 : Type*
  [actK𝓕 : MulAction K 𝓕]
  W : Type*
  [grpW : Group W]
  [fintypeW : Fintype W]
  Z_Ug : Type*
  [commRingZ : CommRing Z_Ug]
  [algebraZ : Algebra ℂ Z_Ug]
  [dotActionW : MulAction W (Z_Ug →ₐ[ℂ] ℂ)]
  antidominance_pred : (Z_Ug →ₐ[ℂ] ℂ) → Prop

end
