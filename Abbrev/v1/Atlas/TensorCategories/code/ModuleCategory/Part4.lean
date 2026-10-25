/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Structure.v1.Atlas.TensorCategories.code.ModuleCategory
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

attribute [reassoc] ModuleFunctor.strIso_natural

attribute [reassoc (attr := simp)] ModuleFunctor.strIso_assoc

attribute [reassoc (attr := simp)] ModuleFunctor.strIso_unit

attribute [reassoc] ModuleNatTrans.compatibility

/-- Alias for `ModuleNatTrans` matching the textbook numbering in EGNO. -/
abbrev Definition_2_12_1 := @ModuleNatTrans

end CategoryTheory
