/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleFunctorCategoryAbelianInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.TensorCategories.code.ModuleFunctorAbelianDefs
set_option maxHeartbeats 400000

set_option linter.all false

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory

/-- Corollary 2.12.3 (EGNO): The category of module functors between two finite left
`C`-module categories is abelian; this packages the existence statement
`moduleFunctorCategoryAbelian` as a chosen instance. -/
noncomputable def corollary_2_12_3
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [FiniteModuleCategory C M]
    {N : Type u₃} [Category.{v₃} N] [LeftModuleCategory C N]
    [FiniteModuleCategory C N] :
    Abelian (ModuleFunctor C M N) :=
  moduleFunctorCategoryAbelian.some

end CategoryTheory
