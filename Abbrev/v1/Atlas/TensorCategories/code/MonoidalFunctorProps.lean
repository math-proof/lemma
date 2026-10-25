/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalFunctorProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Theorem.v1.Atlas.TensorCategories.code.MonoidalFunctorProps
set_option maxHeartbeats 800000


namespace TensorCategories.MonoidalFunctorProps

open CategoryTheory MonoidalCategory Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- EGNO Definition 1.4.1: a monoidal functor `F : C ⥤ D`, expressed as the existence of
a `Functor.Monoidal` structure on `F`. -/
abbrev Definition_1_4_1_MonoidalFunctor (C : Type*) [Category C] [MonoidalCategory C]
    (D : Type*) [Category D] [MonoidalCategory D] (F : C ⥤ D) := F.Monoidal

/-- EGNO Definition 1.4.1 (natural transformations): a monoidal natural transformation
between lax monoidal functors. -/
abbrev def_1_4_1_MonoidalNatTrans
    {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (η : F ⟶ G) := NatTrans.IsMonoidal η

/-- EGNO Definition 1.4.5: a monoidal natural transformation between lax monoidal
functors. -/
abbrev def_1_4_5_MonoidalNatTrans
    {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (η : F ⟶ G) := NatTrans.IsMonoidal η

end TensorCategories.MonoidalFunctorProps
