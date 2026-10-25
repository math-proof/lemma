/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleRigidityCompat.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Theorem.v1.Atlas.TensorCategories.code.ModuleRigidityCompat
set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

namespace ExactModuleCategory

open Category MonoidalCategory LeftModCat

section Construction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [LeftRigidCategory C]
         {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
         [hMEC : ModuleEvalCoeval C M]

/-- Shorthand for the evaluation morphism `(ᘁP) ⊗ P ⟶ 𝟙_ C` supplied by `ModuleEvalCoeval`. -/
abbrev ev (P : C) : (ᘁP : C) ⊗ P ⟶ 𝟙_ C :=
  hMEC.modEval P

/-- Shorthand for the coevaluation morphism `𝟙_ C ⟶ P ⊗ (ᘁP)` supplied by `ModuleEvalCoeval`. -/
abbrev coev (P : C) : 𝟙_ C ⟶ P ⊗ (ᘁP : C) :=
  hMEC.modCoeval P

end Construction
end ExactModuleCategory
end CategoryTheory
