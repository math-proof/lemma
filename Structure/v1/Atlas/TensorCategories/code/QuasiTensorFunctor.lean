/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuasiTensorFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u v₁ u₁ w


namespace TensorCategories

/-- Definition 1.14.1 (Etingof–Gelaki–Nikshych–Ostrik): A quasi-tensor functor
between abelian monoidal categories `C` and `D` over a field `k`. It consists of an
exact (mono- and epi-preserving) faithful functor `F` equipped with natural
isomorphisms `J X Y : F X ⊗ F Y ≅ F (X ⊗ Y)` and a unit isomorphism
`F (𝟙_ C) ≅ 𝟙_ D`. -/
structure QuasiTensorFunctor
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] where
  F : C ⥤ D
  faithful : F.Faithful
  preservesMono : F.PreservesMonomorphisms
  preservesEpi : F.PreservesEpimorphisms
  J : ∀ (X Y : C), F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  J_natural_left : ∀ {X X' : C} (f : X ⟶ X') (Y : C),
    (F.map f ▷ F.obj Y) ≫ (J X' Y).hom = (J X Y).hom ≫ F.map (f ▷ Y)
  J_natural_right : ∀ (X : C) {Y Y' : C} (g : Y ⟶ Y'),
    (F.obj X ◁ F.map g) ≫ (J X Y').hom = (J X Y).hom ≫ F.map (X ◁ g)
  unitIso : F.obj (𝟙_ C) ≅ 𝟙_ D

/-- Definition 1.14.1 (Etingof–Gelaki–Nikshych–Ostrik): A tensor functor between
abelian monoidal categories `C` and `D` over a field `k` is an exact faithful
functor `F` equipped with a monoidal structure (coherent associativity and unit
isomorphisms). -/
structure TensorFunctor
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
    (D : Type u₁) [Category.{v₁} D] [MonoidalCategory D] [Abelian D] where
  F : C ⥤ D
  faithful : F.Faithful
  preservesMono : F.PreservesMonomorphisms
  preservesEpi : F.PreservesEpimorphisms
  monoidal : F.Monoidal

end TensorCategories
