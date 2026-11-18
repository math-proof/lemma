module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctorProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
public import Def.v1.Atlas.TensorCategories.code.ExactModuleCategory.Part4
public import Instance.v1.Atlas.TensorCategories.code.QuasiTensorFunctorProjective.Part2
public section
set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w

namespace CategoryTheory

/-- A functor `F : C ⥤ D` is surjective (in the sense used here) if every object
of `D` is a subquotient of some `F.obj X`: there exist a monomorphism into
`F.obj X` and an epimorphism onto `Y` sharing a common source. -/
class Functor.IsSurjective {C : Type u} [Category.{v} C] {D : Type u₁} [Category.{v₁} D]
    (F : C ⥤ D) : Prop where
  surj : ∀ (Y : D), ∃ (X : C) (A : D) (m : A ⟶ F.obj X) (e : A ⟶ Y), Mono m ∧ Epi e

/-- A quasi-tensor functor between abelian monoidal categories, packaged here as a
class: an additive monoidal functor preserving monomorphisms and epimorphisms. -/
class QuasiTensorFunctor (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] where
  F : C ⥤ D
  monoidal : F.Monoidal
  additive : F.Additive
  preservesMono : F.PreservesMonomorphisms
  preservesEpi : F.PreservesEpimorphisms

/-- A surjective quasi-tensor functor is one whose underlying functor is surjective. -/
class SurjectiveQuasiTensorFunctor (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
    extends QuasiTensorFunctor k C D where
  surjective : F.IsSurjective

end CategoryTheory
