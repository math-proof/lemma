/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Definition_2_1_6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.IsomorphismClasses
import Instance.v1.Atlas.TensorCategories.code.Definition_2_1_6
universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- Setoid on the subtype of simple objects of `M`, identifying objects related by an
isomorphism. -/
def simpleIsoSetoid (M : Type u₁) [Category.{v₁} M] [Limits.HasZeroMorphisms M] :
    Setoid {X : M // Simple X} where
  r := fun ⟨X, _⟩ ⟨Y, _⟩ => Nonempty (X ≅ Y)
  iseqv := ⟨fun ⟨X, _⟩ => ⟨Iso.refl X⟩,
            fun ⟨f⟩ => ⟨f.symm⟩,
            fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

/-- The set of isomorphism classes of simple objects of `M`. -/
def SimpleIsoClasses (M : Type u₁) [Category.{v₁} M] [Limits.HasZeroMorphisms M] : Type u₁ :=
  _root_.Quotient (simpleIsoSetoid M)

/-- The rank of a module category `M`: the number of isomorphism classes of simple
objects, defined when this set is finite. -/
noncomputable def moduleCategoryRank (M : Type u₁) [Category.{v₁} M]
    [Limits.HasZeroMorphisms M] [Fintype (SimpleIsoClasses M)] : ℕ :=
  Fintype.card (SimpleIsoClasses M)

end CategoryTheory
