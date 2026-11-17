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
public import Structure.v1.Atlas.LieGroups.code.DModuleApplications.Part2

@[expose] public section

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

def IrredKEquivDModule.IsIsomorphic (S : SmoothVarietyWithGroupAction)
    (M N : IrredKEquivDModule S) : Prop :=
  Nonempty (M.carrier ≃ₗ[S.DX] N.carrier)

end
