/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part2
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory

open LeftModCat

attribute [reassoc] LeftModuleCategory.actTensorHom_def

attribute [reassoc, simp] LeftModuleCategory.actWhiskerLeft_id

attribute [reassoc, simp] LeftModuleCategory.actId_whiskerRight

attribute [reassoc (attr := simp)] LeftModuleCategory.actTensorHom_comp

attribute [reassoc] LeftModuleCategory.actAssociator_naturality

attribute [reassoc] LeftModuleCategory.actLeftUnitor_naturality

attribute [reassoc (attr := simp)] LeftModuleCategory.actPentagon

attribute [reassoc (attr := simp)] LeftModuleCategory.actTriangle

/-- Definition 2.1.6 (EGNO): A predicate `P : M → Prop` defines a module subcategory of the
left module category `M` if it is closed under the action of `C`, i.e. `P N` implies
`P (X ⊗ᵐ N)` for every `X : C`. -/
class IsModuleSubcategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategoryStruct C M]
    (P : M → Prop) : Prop where
  closed_under_action : ∀ (X : C) (N : M), P N → P (X ⊗ᵐ N)

end CategoryTheory
