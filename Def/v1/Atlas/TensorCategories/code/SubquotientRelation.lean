/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SubquotientRelation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Abbrev.v1.Atlas.TensorCategories.code.SubquotientRelation
set_option maxHeartbeats 400000

open CategoryTheory CategoryTheory.ExactModuleCategory MonoidalCategory Limits

universe u₁ v₁ u₂ v₂


/-- The relation on simple objects of a left `C`-module category which holds when one is a
subquotient of `X ⊗ Y` for some `X ∈ C`; this is the equivalence used to decompose an exact
module category. -/
def subquotientRelation
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] [HasZeroMorphisms M] :
    SimpleObj M → SimpleObj M → Prop :=
  fun X Y => IrrRelated C M X.val Y.val

