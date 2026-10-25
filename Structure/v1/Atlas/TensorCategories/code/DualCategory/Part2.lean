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
import Def.v1.Atlas.TensorCategories.code.DualCategory.Part8
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

/-- A morphism in the double-dual category `(C*_M)*_M`: a natural transformation
between the underlying functors compatible with the `C*_M`-module structures. -/
structure DoubleDualHom [inst : LeftModuleCategory (DualCatObj C M) M]
    (F G : DoubleDualObj C M) where
  natTrans : F.toFunctor ⟶ G.toFunctor
  comm : ∀ (P : DualCatObj C M) (N : M),
    natTrans.app (P ⊗ᵐ N) ≫ (G.strIso P N).hom =
      (F.strIso P N).hom ≫ P ◁ᵐ (natTrans.app N)

end DualCatObj
end CategoryTheory
