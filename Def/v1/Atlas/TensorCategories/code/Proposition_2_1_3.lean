/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_2_1_3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.Category
import Structure.v1.Atlas.TensorCategories.code.Proposition_2_1_3
set_option maxHeartbeats 3200000
set_option autoImplicit false

open CategoryTheory MonoidalCategory Category

universe v₁ v₂ u₁ u₂


/-- Convert `C`-module category data on `M` into a monoidal functor `C ⥤ End(M)`. -/
noncomputable def moduleCatToMonoidalFunctor
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (d : ModuleCategoryData C M) : MonoidalFunctorToEnd C M where
  toFunctor :=
    { obj := fun X =>
        { obj := fun N => d.actObj X N
          map := fun f => d.actWhiskerLeft X f
          map_id := fun N => d.actWhiskerLeft_id X N
          map_comp := fun f g => d.actWhiskerLeft_comp X f g }
      map := fun {X₁ X₂} f =>
        { app := fun N => d.actWhiskerRight f N
          naturality := fun {N₁ N₂} g => (d.actWhisker_comm f g).symm }
      map_id := fun X => by ext N; exact d.actWhiskerRight_id X N
      map_comp := fun {X₁ X₂ X₃} f g => by ext N; exact d.actWhiskerRight_comp f g N }
  unitIso :=
    NatIso.ofComponents (fun N => d.actLeftUnitor N) (fun f => d.actLeftUnitor_naturality f)
  tensorIso := fun X Y =>
    NatIso.ofComponents (fun N => d.actAssociator X Y N)
      (fun f => d.actAssociator_naturality_N X Y f)
  pentagon := fun X Y Z N => by
    simp only [Functor.comp_obj, NatIso.ofComponents_hom_app]
    exact (d.actPentagon X Y Z N).symm
  triangle := fun X N => by
    simp only [NatIso.ofComponents_hom_app]
    exact d.actTriangle X N

/-- Convert a monoidal functor `C ⥤ End(M)` into `C`-module category data on `M`. -/
noncomputable def monoidalFunctorToModuleCat
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (F : MonoidalFunctorToEnd C M) : ModuleCategoryData C M where
  actObj := fun X N => (F.toFunctor.obj X).obj N
  actWhiskerLeft := fun X {_ _} f => (F.toFunctor.obj X).map f
  actWhiskerRight := fun {_ _} f N => (F.toFunctor.map f).app N
  actAssociator := fun X Y N => (F.tensorIso X Y).app N
  actLeftUnitor := fun N => F.unitIso.app N
  actWhiskerLeft_id := fun X N => (F.toFunctor.obj X).map_id N
  actWhiskerLeft_comp := fun X {_ _ _} f g => (F.toFunctor.obj X).map_comp f g
  actWhiskerRight_id := fun X N => NatTrans.congr_app (F.toFunctor.map_id X) N
  actWhiskerRight_comp := fun {_ _ _} f g N => NatTrans.congr_app (F.toFunctor.map_comp f g) N
  actWhisker_comm := fun {_ _} f {_ _} g => ((F.toFunctor.map f).naturality g).symm
  actLeftUnitor_naturality := fun {_ _} f => F.unitIso.hom.naturality f
  actAssociator_naturality_N := fun X Y {_ _} f => (F.tensorIso X Y).hom.naturality f
  actPentagon := fun X Y Z N => (F.pentagon X Y Z N).symm
  actTriangle := fun X N => F.triangle X N

/-- Proposition 2.1.3 (Etingof–Gelaki–Nikshych–Ostrik): Structures of a
`C`-module category on `M` are in natural bijection with monoidal functors
`F : C ⥤ End(M)`. -/
noncomputable def Proposition_2_1_3_moduleCat_equiv_monoidalFunctor
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M]
    : ModuleCategoryData C M ≃ MonoidalFunctorToEnd C M where
  toFun := moduleCatToMonoidalFunctor
  invFun := monoidalFunctorToModuleCat
  left_inv d := by
    cases d
    simp only [moduleCatToMonoidalFunctor, monoidalFunctorToModuleCat, Iso.app,
      NatIso.ofComponents, Functor.comp_obj]
    congr
  right_inv F := by
    cases F
    simp only [moduleCatToMonoidalFunctor, monoidalFunctorToModuleCat, Iso.app,
      NatIso.ofComponents, Functor.comp_obj]
    congr 1

