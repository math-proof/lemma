/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecInstances.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Abbrev.v1.Atlas.TensorCategories.code.TensorCategoryDef.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.TensorCategoryDef
public import Instance.v1.Atlas.TensorCategories.code.VecInstances

@[expose] public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u


noncomputable section

namespace VecInstances

section AutomaticInstances

variable (k : Type u) [Field k]


example : Category (Vec k) := inferInstance

example : Preadditive (Vec k) := inferInstance

example : Linear k (Vec k) := inferInstance

example : Abelian (Vec k) := inferInstance


example : MonoidalCategory (Vec k) := inferInstance

example : MonoidalPreadditive (Vec k) := inferInstance

example : MonoidalLinear k (Vec k) := inferInstance

example : BraidedCategory (Vec k) := inferInstance

example : SymmetricCategory (Vec k) := inferInstance

example : MonoidalClosed (Vec k) := inferInstance


-- Mathlib registers only `RightRigidCategory (FGModuleCat K)`.
-- `LeftRigidCategory` / `RigidCategory` are existing BraidedCategory constructions,
-- not registered as instances (Mathlib: "not canonical enough"). Use those defs.
example : RigidCategory (Vec k) := BraidedCategory.rigidCategoryOfRightRigidCategory

example : RightRigidCategory (Vec k) := inferInstance

example : LeftRigidCategory (Vec k) := BraidedCategory.leftRigidCategoryOfRightRigidCategory


example : HasFiniteLimits (Vec k) := inferInstance

example : HasFiniteColimits (Vec k) := inferInstance

example : HasFiniteCoproducts (Vec k) := inferInstance

example : HasBinaryBiproducts (Vec k) := inferInstance


example : HasForget₂ (Vec k) (ModuleCat k) := inferInstance


example (X Y : Vec k) : Module.Finite k (X ⟶ Y) := inferInstance


example : 𝟙_ (Vec k) = FGModuleCat.of k k := rfl


example : Algebra k (End (𝟙_ (Vec k))) := inferInstance

end AutomaticInstances
end VecInstances
end
