/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_3_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
public import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Class.v1.Atlas.TensorCategories.code.Definition_2_3_1
@[expose] public section

open CategoryTheory CategoryTheory.Limits
open LeftModCat

universe u₁ v₁ u₂ v₂


namespace CategoryTheory

attribute [instance] AbelianModuleCategory.abelian

attribute [instance] AbelianModuleCategory.linear

attribute [instance] AbelianModuleCategory.moduleStruct

attribute [instance] AbelianModuleCategory.moduleCategory

/-- Definition 2.3.1 (alias): a module category satisfying the abelian, linear,
finiteness, and exactness conditions packaged in `AbelianModuleCategory`. -/
abbrev Definition_2_3_1 := @AbelianModuleCategory

/-- Convenience alias for `AbelianModuleCategory`. -/
abbrev IsAbelianModuleCategory := @AbelianModuleCategory

end CategoryTheory
