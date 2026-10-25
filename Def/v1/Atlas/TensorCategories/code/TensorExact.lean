/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorExact.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Abelian.Basic
import Instance.v1.Atlas.TensorCategories.code.TensorExact
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits Opposite

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

section ExactFunctors

/-- The left-tensor functor `X ⊗ -` in a rigid category is exact, packaged as an `exactFunctor`. -/
noncomputable def tensorLeft_exact (X : C) :
    exactFunctor C C (tensorLeft X) :=
  ⟨tensorLeft_preservesFiniteLimits X, tensorLeft_preservesFiniteColimits X⟩

/-- The right-tensor functor `- ⊗ X` in a rigid category is exact, packaged as an `exactFunctor`. -/
noncomputable def tensorRight_exact (X : C) :
    exactFunctor C C (tensorRight X) :=
  ⟨tensorRight_preservesFiniteLimits X, tensorRight_preservesFiniteColimits X⟩

/-- The right dualization functor `Cᵒᵖ ⥤ C` sending `X ↦ Xᘁ` and a morphism to its right adjoint mate. -/
noncomputable def rightDualizationFunctor : Cᵒᵖ ⥤ C where
  obj X := (X.unop)ᘁ
  map f := (f.unop)ᘁ
  map_id X := by simp [rightAdjointMate_id]
  map_comp f g := by simp [comp_rightAdjointMate]

/-- The left dualization functor `Cᵒᵖ ⥤ C` sending `X ↦ ᘁX` and a morphism to its left adjoint mate. -/
noncomputable def leftDualizationFunctor : Cᵒᵖ ⥤ C where
  obj X := ᘁ(X.unop)
  map f := ᘁ(f.unop)
  map_id X := by simp [leftAdjointMate_id]
  map_comp f g := by simp [comp_leftAdjointMate]

/-- The right adjoint mate is a bijection `Hom(X, Y) ≃ Hom(Yᘁ, Xᘁ)` induced by the rigid structure. -/
noncomputable def rightAdjointMateEquiv (X Y : C) : (X ⟶ Y) ≃ (Yᘁ ⟶ Xᘁ) :=
  ((Equiv.mk (fun f => f ≫ (ρ_ Y).inv) (fun f => f ≫ (ρ_ Y).hom)
      (by intro f; simp) (by intro f; simp)).trans
  (((tensorLeftHomEquiv X Y (Yᘁ) (𝟙_ C)).symm).trans
  (((tensorRightHomEquiv (Yᘁ) X (Xᘁ) (𝟙_ C))).trans
  (Equiv.mk (fun f => f ≫ (λ_ (Xᘁ)).hom) (fun f => f ≫ (λ_ (Xᘁ)).inv)
      (by intro f; simp) (by intro f; simp)))))

end ExactFunctors
end CategoryTheory
