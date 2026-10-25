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
import Theorem.v1.Atlas.TensorCategories.code.MonoidalFunctorProps.Part2
set_option maxHeartbeats 800000


namespace TensorCategories.MonoidalFunctorProps

open CategoryTheory MonoidalCategory Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/-- A monoidal functor preserves exact pairings: if `(X, Y)` is an exact pairing in `C`,
then `(F X, F Y)` is an exact pairing in `D`, with evaluation and coevaluation conjugated
by the monoidal structure isomorphisms. -/
noncomputable instance monoidalFunctor_exactPairing
    (F : C ⥤ D) [F.Monoidal] (X Y : C) [ExactPairing X Y] :
    ExactPairing (F.obj X) (F.obj Y) where
  coevaluation' :=
    (Monoidal.εIso F).hom ≫ F.map (ExactPairing.coevaluation X Y) ≫ (Monoidal.μIso F X Y).inv
  evaluation' :=
    (Monoidal.μIso F Y X).hom ≫ F.map (ExactPairing.evaluation X Y) ≫ (Monoidal.εIso F).inv
  coevaluation_evaluation' := by
    simp only [Monoidal.εIso_hom, Monoidal.εIso_inv, Monoidal.μIso_hom, Monoidal.μIso_inv,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [Monoidal.map_associator_inv' F Y X Y]
    simp only [Category.assoc, Monoidal.whiskerLeft_δ_μ_assoc, Monoidal.whiskerRight_δ_μ_assoc]
    rw [LaxMonoidal.μ_natural_right_assoc F Y (ExactPairing.coevaluation X Y)]
    rw [OplaxMonoidal.δ_natural_left_assoc F (ExactPairing.evaluation X Y) Y]
    slice_lhs 3 5 => rw [← F.map_comp, ← F.map_comp]
    rw [ExactPairing.coevaluation_evaluation, F.map_comp]
    simp only [Category.assoc]
    rw [LaxMonoidal.right_unitality F Y]
    simp only [Category.assoc]
    rw [Monoidal.map_leftUnitor_inv F Y]
    simp only [Category.assoc, Monoidal.μ_δ_assoc, Monoidal.whiskerRight_ε_η, Category.comp_id]
  evaluation_coevaluation' := by
    simp only [Monoidal.εIso_hom, Monoidal.εIso_inv, Monoidal.μIso_hom, Monoidal.μIso_inv,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.comp_whiskerRight, Category.assoc]
    rw [Monoidal.map_associator' F X Y X]
    simp only [Category.assoc, Monoidal.whiskerRight_δ_μ_assoc, Monoidal.whiskerLeft_δ_μ_assoc]
    rw [LaxMonoidal.μ_natural_left_assoc F (ExactPairing.coevaluation X Y) X]
    rw [OplaxMonoidal.δ_natural_right_assoc F X (ExactPairing.evaluation X Y)]
    slice_lhs 3 5 => rw [← F.map_comp, ← F.map_comp]
    rw [ExactPairing.evaluation_coevaluation, F.map_comp]
    simp only [Category.assoc]
    rw [LaxMonoidal.left_unitality F X]
    simp only [Category.assoc]
    rw [Monoidal.map_rightUnitor_inv F X]
    simp only [Category.assoc, Monoidal.μ_δ_assoc, Monoidal.whiskerLeft_ε_η, Category.comp_id]

section Exercise_1_10_15

open Category

/-- Part of EGNO Exercise 1.10.15: a monoidal natural transformation between strong
monoidal functors has invertible component at the unit object. -/
noncomputable instance monoidalNatTrans_isIso_unit
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal] :
    IsIso (α.app (𝟙_ C)) := by
  have h := NatTrans.IsMonoidal.unit (τ := α)
  have hcomp : IsIso (LaxMonoidal.ε F ≫ α.app (𝟙_ C)) := h ▸ (Monoidal.εIso G).isIso_hom
  exact IsIso.of_isIso_comp_left (LaxMonoidal.ε F) (α.app (𝟙_ C))

/-- Part of EGNO Exercise 1.10.15: a monoidal natural transformation between strong
monoidal functors has invertible component at a tensor product whenever it has invertible
components at the factors. -/
noncomputable instance monoidalNatTrans_isIso_tensor
    (F G : C ⥤ D) [F.Monoidal] [G.Monoidal] (α : F ⟶ G) [α.IsMonoidal]
    (X Y : C) [IsIso (α.app X)] [IsIso (α.app Y)] :
    IsIso (α.app (X ⊗ Y)) := by
  have h := NatTrans.IsMonoidal.tensor (τ := α) X Y
  have hrhs : IsIso ((α.app X ⊗ₘ α.app Y) ≫ LaxMonoidal.μ G X Y) := by
    apply IsIso.comp_isIso
  have hcomp : IsIso (LaxMonoidal.μ F X Y ≫ α.app (X ⊗ Y)) := h ▸ hrhs
  exact IsIso.of_isIso_comp_left (LaxMonoidal.μ F X Y) (α.app (X ⊗ Y))

end Exercise_1_10_15
end TensorCategories.MonoidalFunctorProps
