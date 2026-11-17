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
public import Structure.v1.Atlas.LieGroups.code.DModuleApplications

@[expose] public section

noncomputable section

attribute [instance] SmoothVarietyWithGroupAction.grpK

attribute [instance] SmoothVarietyWithGroupAction.topK

attribute [instance] SmoothVarietyWithGroupAction.connK

attribute [instance] SmoothVarietyWithGroupAction.actKX

attribute [instance] SmoothVarietyWithGroupAction.ringDX

attribute [instance] SmoothVarietyWithGroupAction.algebraDX

attribute [instance] SmoothVarietyWithGroupAction.actKDX

def SmoothVarietyWithGroupAction.stabilizer (S : SmoothVarietyWithGroupAction)
    (x : S.X) : Subgroup S.K :=
  MulAction.stabilizer S.K x

end
