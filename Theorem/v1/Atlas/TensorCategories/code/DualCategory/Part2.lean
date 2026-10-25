/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DualCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Abbrev.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import Instance.v1.Atlas.TensorCategories.code.DualCategory
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

universe v u


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

variable (M : Type u) [Category.{v} M] [LeftModuleCategory C M]

namespace DualCatObj

variable {C M}

attribute [reassoc] Hom.comm

/-- The underlying natural transformation of the identity morphism in `DualCatObj C M`
is the identity natural transformation. -/
@[simp]
theorem id_natTrans (F : DualCatObj C M) :
    (𝟙 F : Hom F F).natTrans = NatTrans.id F.toFunctor := rfl

/-- The underlying natural transformation of a composition in `DualCatObj C M` is the
composition of the underlying natural transformations. -/
@[simp]
theorem comp_natTrans {F G H : DualCatObj C M} (f : F ⟶ G) (g : G ⟶ H) :
    (f ≫ g).natTrans = f.natTrans ≫ g.natTrans := rfl

end DualCatObj
end CategoryTheory
