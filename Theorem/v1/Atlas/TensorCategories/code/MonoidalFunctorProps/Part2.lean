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
import Abbrev.v1.Atlas.TensorCategories.code.MonoidalFunctorProps
set_option maxHeartbeats 800000


namespace TensorCategories.MonoidalFunctorProps

open CategoryTheory MonoidalCategory Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

example (F G : C ⥤ D) [F.LaxMonoidal] [G.LaxMonoidal] (α : F ⟶ G)
    [α.IsMonoidal] :
    LaxMonoidal.ε F ≫ α.app (𝟙_ C) = LaxMonoidal.ε G :=
  NatTrans.IsMonoidal.unit

example (F G : C ⥤ D) [F.LaxMonoidal] [G.LaxMonoidal] (α : F ⟶ G)
    [α.IsMonoidal] (X Y : C) :
    LaxMonoidal.μ F X Y ≫ α.app (X ⊗ Y) =
      (α.app X ⊗ₘ α.app Y) ≫ LaxMonoidal.μ G X Y :=
  NatTrans.IsMonoidal.tensor X Y

example (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G)
    [α.IsMonoidal] (X Y : C) :
    α.app (X ⊗ Y) =
      inv (LaxMonoidal.μ F X Y) ≫ (α.app X ⊗ₘ α.app Y) ≫ LaxMonoidal.μ G X Y := by
  rw [IsIso.eq_inv_comp]
  exact NatTrans.IsMonoidal.tensor X Y

example (F G H : C ⥤ D) [F.LaxMonoidal] [G.LaxMonoidal] [H.LaxMonoidal]
    (α : F ⟶ G) (β : G ⟶ H) [α.IsMonoidal] [β.IsMonoidal] :
    NatTrans.IsMonoidal (α ≫ β) :=
  inferInstance

end TensorCategories.MonoidalFunctorProps
