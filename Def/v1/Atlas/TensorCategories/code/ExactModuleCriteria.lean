/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCriteria.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.HomExactImpliesExact.Part2
import Abbrev.v1.Atlas.TensorCategories.code.ExactModuleCriteria
universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

/-- Proposition 2.10.7 (EGNO), part 2: A module category `M₁` over `C` is exact whenever
every module functor from `M₁` to any nonzero module category `M₂` is exact. -/
@[reducible] noncomputable def Proposition_2_10_7_part2
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M₁ : Type u₂} [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    {M₂ : Type u₃} [Category.{v₃} M₂] [LeftModuleCategory C M₂]
    [NonzeroModuleCategory M₂]
    (h : ∀ (F : ModuleFunctor C M₁ M₂), ModuleFunctorIsExact F) :
    ExactModuleCategory C M₁ :=
  proposition_2_10_7_part2 h

end CategoryTheory
