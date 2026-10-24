/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite

import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v v₂ u u₂

/-- EGNO Definition 1.1.1: a monoidal category is the data of a tensor bifunctor, associativity
constraint, unit object and unit isomorphism, satisfying the pentagon and unit axioms. -/
abbrev Definition_1_1_1 (C : Type u) [Category.{v} C] := MonoidalCategory C

/-- EGNO Definition 1.1.1 (alias): a monoidal category. -/
abbrev EGNO_Definition_1_1_1 (C : Type u) [Category.{v} C] := MonoidalCategory C

/-- EGNO Definition 1.1.1 (short alias): a monoidal category. -/
abbrev def_1_1_1 (C : Type u) [Category.{v} C] := MonoidalCategory C

/-- EGNO Definition 1.2.6: a monoidal category as a sextuple satisfying the pentagon and triangle
axioms. -/
abbrev Definition_1_2_6 (C : Type u) [Category.{v} C] := MonoidalCategory C

/-- EGNO Definition 1.2.6 (alias): a monoidal category. -/
abbrev EGNO_Definition_1_2_6 (C : Type u) [Category.{v} C] := MonoidalCategory C

/-- EGNO Definition 1.2.6 (short alias): a monoidal category. -/
abbrev def_1_2_6 (C : Type u) [Category.{v} C] := MonoidalCategory C

section Definition_1_1_1_components

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- The tensor product bifunctor `⊗` of a monoidal category, viewed as a function on objects. -/
def Definition_1_1_1.tensorObj : C → C → C := fun X Y => X ⊗ Y

/-- The associativity isomorphism `a_{X,Y,Z} : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z)`. -/
def Definition_1_1_1.associator (X Y Z : C) : (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z) := α_ X Y Z

/-- The unit object `1` of a monoidal category. -/
def Definition_1_1_1.unitObject : C := 𝟙_ C

/-- The unit isomorphism `ι : 𝟙_ C ⊗ 𝟙_ C ≅ 𝟙_ C` realised as the left unitor of the unit. -/
def Definition_1_1_1.unitIso : (𝟙_ C) ⊗ (𝟙_ C) ≅ 𝟙_ C := λ_ (𝟙_ C)

/-- The left unitor isomorphism `l_X : 𝟙_ C ⊗ X ≅ X`. -/
def Definition_1_1_1.leftUnitor (X : C) : (𝟙_ C) ⊗ X ≅ X := λ_ X

/-- The right unitor isomorphism `r_X : X ⊗ 𝟙_ C ≅ X`. -/
def Definition_1_1_1.rightUnitor (X : C) : X ⊗ (𝟙_ C) ≅ X := ρ_ X

end Definition_1_1_1_components

namespace TensorCategories

/-- EGNO Definition 1.1.1 (TensorCategories namespace short alias): a monoidal category. -/
abbrev def_1_1_1 (C : Type u) [Category.{v} C] := MonoidalCategory C

/-- EGNO Definition 1.2.6 (TensorCategories namespace): a monoidal category as a sextuple
satisfying the pentagon and triangle axioms. -/
abbrev Definition_1_2_6 (C : Type u) [Category.{v} C] := MonoidalCategory C

/-- EGNO Definition 1.2.6 (TensorCategories namespace short alias). -/
abbrev def_1_2_6 (C : Type u) [Category.{v} C] := MonoidalCategory C

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The unit isomorphism `(𝟙_ C) ⊗ (𝟙_ C) ⟶ 𝟙_ C` of EGNO Definition 1.1.1, realised as the
right unitor of the unit. -/
def Definition_1_1_1_unitMorphism : (𝟙_ C) ⊗ (𝟙_ C) ⟶ (𝟙_ C) :=
  (ρ_ (𝟙_ C)).hom

/-- The unit morphism of EGNO Definition 1.1.1 is an isomorphism. -/
instance Definition_1_1_1_unitMorphism_isIso :
    IsIso (Definition_1_1_1_unitMorphism (C := C)) := by
  unfold Definition_1_1_1_unitMorphism
  infer_instance

/-- Left multiplication by the unit object is an equivalence of categories `C ⥤ C`, via
the natural isomorphism given by the left unitor. -/
@[reducible]
noncomputable def Definition_1_1_1_leftMultEquiv :
    (tensorLeft (𝟙_ C) : C ⥤ C).IsEquivalence := by
  have iso : tensorLeft (𝟙_ C) ≅ 𝟭 C := NatIso.ofComponents (fun X => λ_ X) (by simp)
  exact Functor.isEquivalence_of_iso iso.symm

/-- Right multiplication by the unit object is an equivalence of categories `C ⥤ C`, via
the natural isomorphism given by the right unitor. -/
@[reducible]
noncomputable def Definition_1_1_1_rightMultEquiv :
    (tensorRight (𝟙_ C) : C ⥤ C).IsEquivalence := by
  have iso : tensorRight (𝟙_ C) ≅ 𝟭 C := NatIso.ofComponents (fun X => ρ_ X) (by simp)
  exact Functor.isEquivalence_of_iso iso.symm

/-- EGNO Definition 1.1.2: a monoidal subcategory of `C` is a category `D` equipped with a
faithful monoidal functor `ι : D ⥤ C`. -/
structure Definition_1_1_2 (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  D : Type u₂
  [instCat : Category.{v₂} D]
  [instMonoidal : MonoidalCategory D]
  ι : D ⥤ C
  [instFaithful : ι.Faithful]
  instMonoidalFunctor : ι.Monoidal

attribute [instance] Definition_1_1_2.instCat
  Definition_1_1_2.instMonoidal
  Definition_1_1_2.instFaithful

/-- Construct a monoidal subcategory in the sense of EGNO Definition 1.1.2 from any
monoidal `ObjectProperty` on `C`. -/
def Definition_1_1_2.ofFullSubcategory
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (P : ObjectProperty C) [P.IsMonoidal] :
    Definition_1_1_2.{v, v, u, u} C where
  D := P.FullSubcategory
  ι := P.ι
  instMonoidalFunctor := inferInstance

section Definition_1_1_3

open CategoryTheory MonoidalCategory MonoidalOpposite

universe v' u'

/-- EGNO Definition 1.1.3: the opposite monoidal category `C^op`, where the tensor product
is reversed. -/
abbrev Definition_1_1_3 (C : Type u') [Category.{v'} C] [MonoidalCategory C] :=
  MonoidalCategory (MonoidalOpposite C)

/-- EGNO Definition 1.1.3 (alias): the opposite monoidal category. -/
abbrev EGNO_Definition_1_1_3 (C : Type u') [Category.{v'} C] [MonoidalCategory C] :=
  MonoidalCategory (MonoidalOpposite C)

/-- EGNO Definition 1.1.3 (short alias): the opposite monoidal category. -/
abbrev def_1_1_3 (C : Type u') [Category.{v'} C] [MonoidalCategory C] :=
  MonoidalCategory (MonoidalOpposite C)

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C]
