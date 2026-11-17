/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Def.v1.Atlas.TensorCategories.code.MonoidalFunctorDef.Part2
@[expose] public section

open CategoryTheory MonoidalCategory

universe v₁ v₂ u₁ u₂


namespace TensorCategories

attribute [instance] def_1_1_2_MonoidalSubcategory.instCat
  def_1_1_2_MonoidalSubcategory.instMonoidal
  def_1_1_2_MonoidalSubcategory.instFaithful

section MonoidalNatTrans

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- EGNO Definition 1.4.5: a monoidal functor on `F`, expressed as the existence of a
`Functor.Monoidal` structure. -/
abbrev def_1_4_5_MonoidalFunctor (F : C ⥤ D) := F.Monoidal

/-- EGNO Definition 1.5.1: a monoidal natural transformation between lax monoidal
functors, expressed via `NatTrans.IsMonoidal`. -/
abbrev def_1_5_1_MonoidalNatTrans {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (η : F ⟶ G) :=
  NatTrans.IsMonoidal η

/-- EGNO Definition 1.5.1 (isomorphism version): an isomorphism of lax monoidal functors. -/
abbrev def_1_5_1_MonoidalFunctorIso (F G : LaxMonoidalFunctor C D) :=
  F ≅ G

end MonoidalNatTrans
end TensorCategories
