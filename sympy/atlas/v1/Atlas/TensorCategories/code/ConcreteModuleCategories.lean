/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ConcreteModuleCategories.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.ModuleCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.ExactModuleCategory
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import sympy.atlas.v1.Atlas.TensorCategories.code.DeligneTensorProductMonoidal
import sympy.atlas.v1.Atlas.TensorCategories.code.FiniteTensorCategory
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ vₘ w u₁ u₂ u₃ uₘ

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section SelfModuleCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

/-- The left-whiskering map used to view a monoidal category `C` as a left module category
over itself: takes `f : M₁ ⟶ M₂` to `X ◁ f : X ⊗ M₁ ⟶ X ⊗ M₂`. -/
abbrev selfActWhiskerLeft (X : C) {M₁ M₂ : C} (f : M₁ ⟶ M₂) : X ⊗ M₁ ⟶ X ⊗ M₂ := X ◁ f

/-- Every monoidal category `C` is a left module category over itself, with action given by
tensor product. -/
instance selfLeftModuleCategory : LeftModuleCategory C C where
  actObj X Y := X ⊗ Y
  actWhiskerLeft X {M₁ M₂} f := X ◁ f
  actWhiskerRight {X₁ X₂} f N := f ▷ N
  actAssociator X Y N := α_ X Y N
  actLeftUnitor N := λ_ N
  actTensorHom_def _ _ := rfl
  actId_tensorHom_id X N := by simp
  actTensorHom_comp f₁ g₁ f₂ g₂ := by

    slice_lhs 2 3 => rw [whisker_exchange]
    simp [assoc, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp]
  actWhiskerLeft_id X N := by simp
  actId_whiskerRight X N := by simp
  actAssociator_naturality f g h := by

    rw [← MonoidalCategory.tensorHom_def (f ⊗ₘ g) h]
    rw [← MonoidalCategory.tensorHom_def g h]
    rw [← MonoidalCategory.tensorHom_def f (g ⊗ₘ h)]
    exact associator_naturality f g h
  actLeftUnitor_naturality f := leftUnitor_naturality f
  actPentagon X Y Z N := pentagon X Y Z N
  actTriangle X N := triangle X N

end SelfModuleCategory

section SelfExactModuleCategory


variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]

/-- When `C` preserves projectives under tensoring, the self-module structure of `C` over itself
is an exact module category. -/
instance selfExactModuleCategory [TensorPreservesProjective C] :
    ExactModuleCategory C C where
  action_preserves_projective P N :=
    TensorPreservesProjective.tensor_projective P N

end SelfExactModuleCategory

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

section BimoduleCategory

/-- Structure of a right module category over a monoidal category `D`: provides a right
action `ractObj : M → D → M` together with whiskering, associator, and right unitor data. -/
class RightModuleCategoryStruct
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D]
    (M : Type*) [Category M] where
  ractObj : M → D → M
  ractWhiskerLeft {N₁ N₂ : M} (f : N₁ ⟶ N₂) (X : D) :
    ractObj N₁ X ⟶ ractObj N₂ X
  ractWhiskerRight (N : M) {X₁ X₂ : D} (f : X₁ ⟶ X₂) :
    ractObj N X₁ ⟶ ractObj N X₂
  ractAssociator : ∀ (N : M) (X Y : D),
    ractObj (ractObj N X) Y ≅ ractObj N (X ⊗ Y)
  ractRightUnitor : ∀ (N : M), ractObj N (𝟙_ D) ≅ N

/-- Structure of a `(C, D)`-bimodule category on `M`: combines compatible left `C`-action
and right `D`-action data with a middle interchange isomorphism. -/
structure BimoduleCategoryStruct
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (D : Type*) [Category D] [MonoidalCategory D]
    (M : Type*) [Category M] where
  lactObj : C → M → M
  ractObj : M → D → M
  lactWhiskerLeft (X : C) {N₁ N₂ : M} (f : N₁ ⟶ N₂) :
    lactObj X N₁ ⟶ lactObj X N₂
  lactWhiskerRight {X₁ X₂ : C} (f : X₁ ⟶ X₂) (N : M) :
    lactObj X₁ N ⟶ lactObj X₂ N
  ractWhiskerLeft {N₁ N₂ : M} (f : N₁ ⟶ N₂) (Y : D) :
    ractObj N₁ Y ⟶ ractObj N₂ Y
  ractWhiskerRight (N : M) {Y₁ Y₂ : D} (f : Y₁ ⟶ Y₂) :
    ractObj N Y₁ ⟶ ractObj N Y₂
  lactAssociator : ∀ (X Y : C) (N : M),
    lactObj (X ⊗ Y) N ≅ lactObj X (lactObj Y N)
  ractAssociator : ∀ (N : M) (X Y : D),
    ractObj (ractObj N X) Y ≅ ractObj N (X ⊗ Y)
  lactLeftUnitor : ∀ (N : M), lactObj (𝟙_ C) N ≅ N
  ractRightUnitor : ∀ (N : M), ractObj N (𝟙_ D) ≅ N
  middleInterchange : ∀ (X : C) (N : M) (Y : D),
    ractObj (lactObj X N) Y ≅ lactObj X (ractObj N Y)

/-- Definition 2.5.4 (EGNO): a `(C, D)`-bimodule category over a field `k`, where `C` and `D`
are multitensor categories. The data consists of compatible left and right actions on `M`
together with pentagon, triangle, and middle-interchange coherence axioms. -/
class Definition_2_5_4_BimoduleCategory
    (k : Type w) [Field k]
    (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] [TensorCategories.MultitensorCategory k C]
    (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Linear k D] [Abelian D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear k D]
    [RigidCategory D] [TensorCategories.MultitensorCategory k D]
    (M : Type*) [Category M]
    extends BimoduleCategoryStruct C D M where
  leftPentagon : ∀ (X Y Z : C) (N : M),
    (lactWhiskerRight (α_ X Y Z).hom N) ≫
    (lactAssociator X (Y ⊗ Z) N).hom ≫
    (lactWhiskerLeft X (lactAssociator Y Z N).hom) =
    (lactAssociator (X ⊗ Y) Z N).hom ≫
    (lactAssociator X Y (lactObj Z N)).hom
  leftTriangle : ∀ (X : C) (N : M),
    (lactAssociator X (𝟙_ C) N).hom ≫
    (lactWhiskerLeft X (lactLeftUnitor N).hom) =
    (lactWhiskerRight (ρ_ X).hom N)
  rightPentagon : ∀ (N : M) (X Y Z : D),
    (ractWhiskerLeft (ractAssociator N X Y).hom Z) ≫
    (ractAssociator N (X ⊗ Y) Z).hom ≫
    (ractWhiskerRight N (α_ X Y Z).hom) =
    (ractAssociator (ractObj N X) Y Z).hom ≫
    (ractAssociator N X (Y ⊗ Z)).hom
  rightTriangle : ∀ (N : M) (Y : D),
    (ractAssociator N (𝟙_ D) Y).hom ≫
    (ractWhiskerRight N (λ_ Y).hom) =
    (ractWhiskerLeft (ractRightUnitor N).hom Y)
  leftMiddlePentagon : ∀ (X Y : C) (N : M) (Z : D),
    (ractWhiskerLeft (lactAssociator X Y N).hom Z) ≫
    (middleInterchange X (lactObj Y N) Z).hom ≫
    (lactWhiskerLeft X (middleInterchange Y N Z).hom) =
    (middleInterchange (X ⊗ Y) N Z).hom ≫
    (lactAssociator X Y (ractObj N Z)).hom
  rightMiddlePentagon : ∀ (X : C) (N : M) (Y Z : D),
    (ractWhiskerLeft (middleInterchange X N Y).hom Z) ≫
    (middleInterchange X (ractObj N Y) Z).hom ≫
    (lactWhiskerLeft X (ractAssociator N Y Z).hom) =
    (ractAssociator (lactObj X N) Y Z).hom ≫
    (middleInterchange X N (Y ⊗ Z)).hom

/-- Shorthand for `Definition_2_5_4_BimoduleCategory`. -/
abbrev Definition_2_5_4 :=
  @Definition_2_5_4_BimoduleCategory

/-- A `(C, D)`-bimodule category: a category `M` equipped with compatible left `C`- and right
`D`-actions satisfying the pentagon, triangle, and middle interchange coherence axioms. -/
class BimoduleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D]
    (M : Type*) [Category M] extends BimoduleCategoryStruct C D M where
  left_pentagon : ∀ (X Y Z : C) (N : M),
    (lactWhiskerRight (α_ X Y Z).hom N) ≫
    (lactAssociator X (Y ⊗ Z) N).hom ≫
    (lactWhiskerLeft X (lactAssociator Y Z N).hom) =
    (lactAssociator (X ⊗ Y) Z N).hom ≫
    (lactAssociator X Y (lactObj Z N)).hom
  right_pentagon : ∀ (N : M) (X Y Z : D),
    (ractWhiskerLeft (ractAssociator N X Y).hom Z) ≫
    (ractAssociator N (X ⊗ Y) Z).hom ≫
    (ractWhiskerRight N (α_ X Y Z).hom) =
    (ractAssociator (ractObj N X) Y Z).hom ≫
    (ractAssociator N X (Y ⊗ Z)).hom
  middle_assoc : ∀ (X Y : C) (N : M) (Z : D),
    (ractWhiskerLeft (lactAssociator X Y N).hom Z) ≫
    (middleInterchange X (lactObj Y N) Z).hom ≫
    (lactWhiskerLeft X (middleInterchange Y N Z).hom) =
    (middleInterchange (X ⊗ Y) N Z).hom ≫
    (lactAssociator X Y (ractObj N Z)).hom
  left_unit : ∀ (X : C) (N : M),
    (lactAssociator X (𝟙_ C) N).hom ≫
    (lactWhiskerLeft X (lactLeftUnitor N).hom) =
    (lactWhiskerRight (ρ_ X).hom N)
  right_unit : ∀ (N : M) (Y : D),
    (ractAssociator N (𝟙_ D) Y).hom ≫
    (ractWhiskerRight N (λ_ Y).hom) =
    (ractWhiskerLeft (ractRightUnitor N).hom Y)
  right_middle_pentagon : ∀ (X : C) (N : M) (Y Z : D),
    (ractWhiskerLeft (middleInterchange X N Y).hom Z) ≫
    (middleInterchange X (ractObj N Y) Z).hom ≫
    (lactWhiskerLeft X (ractAssociator N Y Z).hom) =
    (ractAssociator (lactObj X N) Y Z).hom ≫
    (middleInterchange X N (Y ⊗ Z)).hom

/-- The EGNO definition of a bimodule category (over a field `k`) yields the underlying
plain `BimoduleCategory` structure by forgetting the linearity/abelian conditions. -/
class BimoduleCategoryViaDeligne
    (k : Type w) [Field k]
    (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] [TensorCategories.MultitensorCategory k C]
    (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Linear k D] [Abelian D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear k D]
    [RigidCategory D] [TensorCategories.MultitensorCategory k D]
    [Abelian Dᴹᵒᵖ] [Linear k Dᴹᵒᵖ]
    (M : Type uₘ) [Category.{vₘ} M] where
  deligne : Unit := ()
  monInst : Unit := ()
  moduleStr : Unit := ()

/-- The bimodule category structure of `C` over itself on both sides: left and right
actions are both given by tensor product, with the middle interchange being the associator. -/
def selfBimoduleCategoryStruct
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] :
    BimoduleCategoryStruct C C C where
  lactObj X N := X ⊗ N
  ractObj N Y := N ⊗ Y
  lactWhiskerLeft X {N₁ N₂} f := X ◁ f
  lactWhiskerRight {X₁ X₂} f N := f ▷ N
  ractWhiskerLeft {N₁ N₂} f Y := f ▷ Y
  ractWhiskerRight N {Y₁ Y₂} f := N ◁ f
  lactAssociator X Y N := α_ X Y N
  ractAssociator N X Y := α_ N X Y
  lactLeftUnitor N := λ_ N
  ractRightUnitor N := ρ_ N
  middleInterchange X N Y := α_ X N Y

/-- Any monoidal category `C` is a `(C, C)`-bimodule category over itself, with all coherence
axioms reduced to the pentagon and triangle identities. -/
instance selfBimoduleCategoryInstance
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] :
    BimoduleCategory C C C where
  __ := selfBimoduleCategoryStruct C
  left_pentagon X Y Z N := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon X Y Z N
  right_pentagon N X Y Z := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon N X Y Z
  middle_assoc X Y N Z := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon X Y N Z
  left_unit X N := by
    simp only [selfBimoduleCategoryStruct]
    exact triangle X N
  right_unit N Y := by
    simp only [selfBimoduleCategoryStruct]
    exact triangle N Y
  right_middle_pentagon X N Y Z := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon X N Y Z

/-- Any multitensor category `C` is a `(C, C)`-bimodule category over itself in the sense of
Definition 2.5.4, with all coherence axioms following from the monoidal pentagon and triangle. -/
noncomputable def selfBimoduleCategory
    (k : Type w) [Field k]
    (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] [TensorCategories.MultitensorCategory k C] :
    Definition_2_5_4_BimoduleCategory k C C C where
  __ := selfBimoduleCategoryStruct C
  leftPentagon X Y Z N := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon X Y Z N
  leftTriangle X N := by
    simp only [selfBimoduleCategoryStruct]
    exact triangle X N
  rightPentagon N X Y Z := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon N X Y Z
  rightTriangle N Y := by
    simp only [selfBimoduleCategoryStruct]
    exact triangle N Y
  leftMiddlePentagon X Y N Z := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon X Y N Z
  rightMiddlePentagon X N Y Z := by
    simp only [selfBimoduleCategoryStruct]
    exact pentagon X N Y Z

/-- A predicate `P` on the objects of a left `C`-module category `M` defines a module
subcategory if it is closed under the left action of `C`. -/
class ModuleSubcategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type*) [Category M] [LeftModuleCategoryStruct C M]
    (P : M → Prop) : Prop where
  action_closed : ∀ (X : C) (N : M), P N → P (LeftModuleCategoryStruct.actObj X N)

end BimoduleCategory

end CategoryTheory
