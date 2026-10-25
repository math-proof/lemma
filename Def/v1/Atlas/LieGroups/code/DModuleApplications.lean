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
import Structure.v1.Atlas.LieGroups.code.DModuleApplications


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
