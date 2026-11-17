/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModuleApplications.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Def.v1.Atlas.LieGroups.code.DModuleApplications


public noncomputable section

attribute [instance] SmoothVarietyWithGroupAction.grpK

attribute [instance] SmoothVarietyWithGroupAction.topK

attribute [instance] SmoothVarietyWithGroupAction.connK

attribute [instance] SmoothVarietyWithGroupAction.actKX

attribute [instance] SmoothVarietyWithGroupAction.ringDX

attribute [instance] SmoothVarietyWithGroupAction.algebraDX

attribute [instance] SmoothVarietyWithGroupAction.actKDX

structure OrbitRepPair (S : SmoothVarietyWithGroupAction) where
  orbit : Set S.X
  orbit_mem : orbit ∈ S.orbits
  basepoint : S.X
  basepoint_mem : basepoint ∈ orbit
  ComponentGroup : Type*
  [compGrpGroup : Group ComponentGroup]
  quotientMap : (MulAction.stabilizer S.K basepoint) →* ComponentGroup
  quotientMap_surjective : Function.Surjective quotientMap
  V : Type*
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module ℂ V]
  compGroupRep : Representation ℂ ComponentGroup V
  V_irreducible : compGroupRep.IsIrreducible

attribute [instance] OrbitRepPair.addCommGroupV

attribute [instance] OrbitRepPair.moduleV

attribute [instance] OrbitRepPair.compGrpGroup

structure IrredKEquivDModule (S : SmoothVarietyWithGroupAction) where
  carrier : Type*
  [addCommGroup : AddCommGroup carrier]
  [moduleC : Module ℂ carrier]
  [moduleDX : Module S.DX carrier]
  [mulActionK : MulAction S.K carrier]
  equivariance : ∀ (k : S.K) (d : S.DX) (m : carrier),
    k • (d • m) = (k • d) • (k • m)
  isIrreducible : IsSimpleModule S.DX carrier

end
