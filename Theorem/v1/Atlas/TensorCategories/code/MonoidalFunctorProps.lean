/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
set_option maxHeartbeats 800000

public section

namespace TensorCategories.MonoidalFunctorProps

open CategoryTheory MonoidalCategory Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

example (F : C ⥤ D) [F.LaxMonoidal] : 𝟙_ D ⟶ F.obj (𝟙_ C) :=
  LaxMonoidal.ε F

example (F : C ⥤ D) [F.LaxMonoidal] (X Y : C) :
    F.obj X ⊗ F.obj Y ⟶ F.obj (X ⊗ Y) :=
  LaxMonoidal.μ F X Y

example (F : C ⥤ D) [F.Monoidal] : IsIso (LaxMonoidal.ε F) :=
  (Monoidal.εIso F).isIso_hom

end TensorCategories.MonoidalFunctorProps
