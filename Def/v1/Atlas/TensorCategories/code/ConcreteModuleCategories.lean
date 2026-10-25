/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ConcreteModuleCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.ModuleCategory.Part5
import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Theorem.v1.Atlas.TensorCategories.code.DeligneTensorProductMonoidal
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite
import Instance.v1.Atlas.TensorCategories.code.ConcreteModuleCategories
set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ


namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section MonoidalFunctorModuleCategory

variable {C : Type u₃} [Category.{v₃} C] [MonoidalCategory C]

variable {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D]

variable (F : C ⥤ D) [F.Monoidal]

/-- The associator isomorphism `F(X ⊗ Y) ⊗ N ≅ F(X) ⊗ (F(Y) ⊗ N)` used to transport a
left module structure along a monoidal functor `F : C ⥤ D`. -/
def monoidalFunctorModAssociator (X Y : C) (N : D) :
    F.obj (X ⊗ Y) ⊗ N ≅ F.obj X ⊗ (F.obj Y ⊗ N) :=
  tensorIso (Functor.Monoidal.μIso F X Y).symm (Iso.refl N) ≪≫ α_ (F.obj X) (F.obj Y) N

/-- The left unitor isomorphism `F(𝟙_C) ⊗ N ≅ N` used to transport a left module structure
along a monoidal functor `F : C ⥤ D`. -/
def monoidalFunctorModLeftUnitor (N : D) :
    F.obj (𝟙_ C) ⊗ N ≅ N :=
  tensorIso (Functor.Monoidal.εIso F).symm (Iso.refl N) ≪≫ λ_ N

/-- Transport of the self left module category structure along a monoidal functor
`F : C ⥤ D`: makes `D` a `C`-module category via the action `X • N := F(X) ⊗ N`. -/
def monoidalFunctorModuleCategoryStruct :
    LeftModuleCategoryStruct C D where
  actObj X Y := F.obj X ⊗ Y
  actWhiskerLeft X {M₁ M₂} f := F.obj X ◁ f
  actWhiskerRight {X₁ X₂} f N := F.map f ▷ N
  actAssociator X Y N := monoidalFunctorModAssociator F X Y N
  actLeftUnitor N := monoidalFunctorModLeftUnitor F N

end MonoidalFunctorModuleCategory
end CategoryTheory
