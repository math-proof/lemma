/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Class.v1.Atlas.TensorCategories.code.ModuleCategory.Part2
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory

namespace LeftModCat

export LeftModuleCategoryStruct (actObj actWhiskerLeft actWhiskerRight actTensorHom
  actAssociator actLeftUnitor)

scoped infixr:70 " ⊗ᵐ " => LeftModuleCategoryStruct.actObj

scoped infixr:81 " ◁ᵐ " => LeftModuleCategoryStruct.actWhiskerLeft

scoped infixl:81 " ▷ᵐ " => LeftModuleCategoryStruct.actWhiskerRight

scoped infixr:70 " ⊗ₘᵐ " => LeftModuleCategoryStruct.actTensorHom

scoped notation "actμ_" => LeftModuleCategoryStruct.actAssociator

scoped notation "actℓ_" => LeftModuleCategoryStruct.actLeftUnitor

end LeftModCat
end CategoryTheory
