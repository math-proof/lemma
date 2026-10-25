/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SurjectiveTensorFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁


/-- A functor `F : C ⥤ D` is surjective when every object of `D` arises as a subquotient of
some `F.obj X`. -/
class IsSurjectiveFunctor
    {C : Type u} [Category.{v} C]
    {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ D) : Prop where
  surj : ∀ (Y : D), ∃ (X : C) (A : D) (m : A ⟶ F.obj X) (e : A ⟶ Y), Mono m ∧ Epi e

/-- A quasi-tensor functor `C ⥤ D` between abelian monoidal categories: a faithful additive
monoidal functor. -/
class QuasiTensorFunctor
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] where
  F : C ⥤ D
  monoidal : F.Monoidal
  additive : F.Additive
  faithful : F.Faithful

/-- A surjective quasi-tensor functor: a quasi-tensor functor whose underlying functor is
surjective in the sense that every target object is a subquotient of an image. -/
class SurjectiveQuasiTensorFunctor
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
    extends QuasiTensorFunctor C D where
  surjective : IsSurjectiveFunctor F

/-- The property that every projective object is also injective; this characterises finite tensor
categories, where projectives and injectives coincide. -/
class ProjectiveIsInjective (C : Type u₁) [Category.{v₁} C] : Prop where
  injective_of_projective : ∀ (Q : C), Projective Q → Injective Q

