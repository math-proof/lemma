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
import Def.v1.Atlas.LieGroups.code.DModuleApplications.Part4


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

attribute [instance] HCGKModule.addCommGroup

attribute [instance] HCGKModule.module

attribute [instance] HCGKModule.lieRingModule

attribute [instance] HCGKModule.lieModule

attribute [instance] HCGKModule.mulAction

structure HCClassifyingDatum (D : HarishChandraData) where
  basepoint : D.𝓕
  orbit : Set D.𝓕
  orbit_eq : orbit = MulAction.orbit D.K basepoint
  K_x : Subgroup D.K
  K_x_eq : K_x = MulAction.stabilizer D.K basepoint
  V : Type*
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module ℂ V]
  stabRep : Representation ℂ K_x V
  V_irreducible : stabRep.IsIrreducible
  lieKx : LieSubalgebra ℂ D.𝔤
  char_lieKx : D.𝔤 →ₗ[ℂ] ℂ
  lieKx_action : lieKx →ₗ[ℂ] (V →ₗ[ℂ] V)
  char_lieKx_acts : ∀ (X : lieKx) (v : V), lieKx_action X v = char_lieKx (X : D.𝔤) • v

end
