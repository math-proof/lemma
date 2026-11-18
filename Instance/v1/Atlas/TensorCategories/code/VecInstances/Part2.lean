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
public import Theorem.v1.Atlas.TensorCategories.code.VecInstances.Part2
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
@[expose] public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u


noncomputable section

namespace VecInstances

section FiniteLength

variable (k : Type u) [Field k]

-- Mathlib registers only `RightRigidCategory (FGModuleCat K)`.
-- `LeftRigidCategory` / `RigidCategory` are existing BraidedCategory constructions,
-- not registered as instances (Mathlib: not canonical enough). Use those defs.
instance : RigidCategory (Vec k) := BraidedCategory.rigidCategoryOfRightRigidCategory
instance : LeftRigidCategory (Vec k) := BraidedCategory.leftRigidCategoryOfRightRigidCategory

/-- `Vec k` is locally finite (Definition 1.12.1): finite-dimensional hom-spaces and
finite-length objects. -/
instance locallyFiniteCategory_vec :
    TensorCategories.LocallyFiniteCategory k (Vec k) where
  homFinite := fun _ _ => inferInstance
  hasFiniteLength := hasFiniteLength_vec k

/-- `Vec k` is a multitensor category in the sense of Definition 1.12.3. -/
instance multitensorCategory_vec :
    TensorCategories.MultitensorCategory k (Vec k) where
  homFinite := fun _ _ => inferInstance
  hasFiniteLength := hasFiniteLength_vec k

end FiniteLength
end VecInstances
end
