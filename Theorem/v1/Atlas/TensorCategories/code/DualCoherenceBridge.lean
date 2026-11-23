/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCoherenceBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
public import Theorem.Category.Atlas.v1.TensorCategories.code.VecInstances
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

public section

namespace FGModuleCat

variable (k : Type u) [Field k]

end FGModuleCat

noncomputable section

universe u

section DisableIndirectPath

variable (k : Type u) [Field k]


attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory in

example : RightRigidCategory (FGModuleCat k) := inferInstance

attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory in

example : LeftRigidCategory (FGModuleCat k) := inferInstance

attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory in

example : RigidCategory (FGModuleCat k) := inferInstance

attribute [-instance] BraidedCategory.rightRigidCategoryOfLeftRigidCategory in

example (V : FGModuleCat k) : (Vᘁ)ᘁ = (Vᘁ)ᘁ := rfl

end DisableIndirectPath
end
