/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ModuleCategoryDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
public import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat

@[expose] public section

open CategoryTheory Category MonoidalCategory LeftModCat

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M]

/-- For a fixed `X ∈ M`, the predicate selecting objects `N` whose simple subquotients are all
related to `X` via the action of `C` (the equivalence relation of Lemma 2.7.6). -/
def moduleSubcategory' (X : M) : M → Prop :=
  fun N => AllSimpleSubquotientsInClass' C X N

end ExactModuleCategory
end CategoryTheory
