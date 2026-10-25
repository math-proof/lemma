/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ExactModuleCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Abbrev.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Noetherian
import Mathlib.RingTheory.Finiteness.Defs
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part3
set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃


namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

namespace ExactModuleCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]

/-- Symmetry of the subquotient witness for `IrrRelated` when `X` is simple: from a
subquotient witness `Y ↪↠ L ⊗ X`, produce some `S` and a subquotient witness `X ↪↠ S ⊗ Y`.-/
structure IrrRelatedEquivalence
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
    [HasZeroMorphisms M] where
  refl : ∀ (X : M), IrrRelated C M X X
  symm : ∀ {X Y : M} [Simple X], IrrRelated C M X Y → IrrRelated C M Y X
  trans : ∀ {X Y Z : M}, IrrRelated C M X Y → IrrRelated C M Y Z → IrrRelated C M X Z

end ExactModuleCategory
end CategoryTheory
