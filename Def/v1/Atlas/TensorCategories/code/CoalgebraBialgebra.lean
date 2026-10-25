/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CoalgebraBialgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Products.Basic
import Theorem.v1.Atlas.TensorCategories.code.CoalgebraBialgebra.Part2
set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory

universe u v w


section Thm_1_21_1

open MonoidalCategory

variable (k : Type u) [CommRing k]

variable (C : Type v) [Category.{w} C] [MonoidalCategory C] [Preadditive C] [Linear k C]

variable (F : C ⥤ ModuleCat.{u} k) [F.Monoidal] [F.Faithful]

set_option synthInstance.maxHeartbeats 400000

/-- The counit `End(F) → k` of the bialgebra `End(F)` of a fiber functor `F`: evaluate the
natural transformation at the unit object and read off its action on `1 ∈ k`. -/
noncomputable def endF_counit_def : End F →ₗ[k] k where
  toFun η :=
    ((Functor.Monoidal.εIso F).hom ≫ η.app (𝟙_ C) ≫
      (Functor.Monoidal.εIso F).inv).hom (1 : k)
  map_add' η₁ η₂ := by
    have : (η₁ + η₂).app (𝟙_ C) = η₁.app (𝟙_ C) + η₂.app (𝟙_ C) := rfl
    simp only [this, Preadditive.add_comp, Preadditive.comp_add]
    rfl
  map_smul' r η := by
    have h1 : (r • η).app (𝟙_ C) = r • η.app (𝟙_ C) := rfl
    simp only [h1, RingHom.id_apply]
    suffices h : (Functor.Monoidal.εIso F).hom ≫ (r • η.app (𝟙_ C)) ≫
      (Functor.Monoidal.εIso F).inv =
      r • ((Functor.Monoidal.εIso F).hom ≫ η.app (𝟙_ C) ≫
        (Functor.Monoidal.εIso F).inv) by
      simp only [h]; rfl
    rw [show (r • η.app (𝟙_ C)) ≫ (Functor.Monoidal.εIso F).inv =
        r • (η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv) from
        Linear.smul_comp _ _ _ _ _ _]
    rw [show (Functor.Monoidal.εIso F).hom ≫
        (r • (η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv)) =
        r • ((Functor.Monoidal.εIso F).hom ≫
          (η.app (𝟙_ C) ≫ (Functor.Monoidal.εIso F).inv)) from
        Linear.comp_smul _ _ _ _ _ _]

/-- The bifunctor `(X, Y) ↦ F(X) ⊗ F(Y)` from `C × C` to `ModuleCat k`, used to express
the multiplicative structure on `End(F)`. -/
noncomputable def functorSelfTensor :
    (C × C) ⥤ ModuleCat.{u} k where
  obj XY := F.obj XY.1 ⊗ F.obj XY.2
  map f := F.map f.1 ⊗ₘ F.map f.2
  map_id XY := by
    change F.map (𝟙 XY.1) ⊗ₘ F.map (𝟙 XY.2) = 𝟙 _
    rw [F.map_id, F.map_id, id_tensorHom_id]
  map_comp f g := by
    change F.map (f.1 ≫ g.1) ⊗ₘ F.map (f.2 ≫ g.2) = _
    rw [F.map_comp, F.map_comp, tensorHom_comp_tensorHom]

end Thm_1_21_1
