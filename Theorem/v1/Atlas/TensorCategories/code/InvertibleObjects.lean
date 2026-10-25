/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/InvertibleObjects.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Def.v1.Atlas.TensorCategories.code.InvertibleObjects
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [RigidCategory C]

section LeftDualIsoRightDual

variable (X : C) [HasRightDual X] [IsIso (ε_ X (Xᘁ))] [IsIso (η_ X (Xᘁ))]

omit [RigidCategory C] in
/-- Zigzag identity for the inverses of evaluation and coevaluation morphisms (one of
the two compatibility laws used to upgrade `Xᘁ` to a left dual when `ε`, `η` are iso). -/
lemma zigzag_inv_eval_coeval :
    (inv (ε_ X Xᘁ) ▷ Xᘁ) ≫ (α_ Xᘁ X Xᘁ).hom ≫ (Xᘁ ◁ inv (η_ X Xᘁ)) =
    (λ_ Xᘁ).hom ≫ (ρ_ Xᘁ).inv := by
  have h : (Xᘁ ◁ η_ X Xᘁ) ≫ (α_ Xᘁ X Xᘁ).inv ≫ (ε_ X Xᘁ ▷ Xᘁ) =
      (ρ_ Xᘁ).hom ≫ (λ_ Xᘁ).inv :=
    ExactPairing.coevaluation_evaluation' (X := X) (Y := Xᘁ)
  have cancel : ((Xᘁ ◁ η_ X Xᘁ) ≫ (α_ Xᘁ X Xᘁ).inv ≫ (ε_ X Xᘁ ▷ Xᘁ)) ≫
      ((inv (ε_ X Xᘁ) ▷ Xᘁ) ≫ (α_ Xᘁ X Xᘁ).hom ≫ (Xᘁ ◁ inv (η_ X Xᘁ))) =
      𝟙 (Xᘁ ⊗ 𝟙_ C) := by
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [← comp_whiskerRight, IsIso.hom_inv_id, id_whiskerRight]
    simp [Iso.inv_hom_id_assoc, ← MonoidalCategory.whiskerLeft_comp]
  rw [h] at cancel
  rw [← cancel_epi ((ρ_ Xᘁ).hom ≫ (λ_ Xᘁ).inv), cancel]
  simp

omit [RigidCategory C] in
/-- Dual zigzag identity for the inverses of coevaluation and evaluation, completing the
exact-pairing axioms for the pair `(Xᘁ, X)`. -/
lemma zigzag_inv_coeval_eval :
    (X ◁ inv (ε_ X Xᘁ)) ≫ (α_ X Xᘁ X).inv ≫ (inv (η_ X Xᘁ) ▷ X) =
    (ρ_ X).hom ≫ (λ_ X).inv := by
  have h : (η_ X Xᘁ ▷ X) ≫ (α_ X Xᘁ X).hom ≫ (X ◁ ε_ X Xᘁ) =
      (λ_ X).hom ≫ (ρ_ X).inv :=
    ExactPairing.evaluation_coevaluation' (X := X) (Y := Xᘁ)
  have cancel : ((η_ X Xᘁ ▷ X) ≫ (α_ X Xᘁ X).hom ≫ (X ◁ ε_ X Xᘁ)) ≫
      ((X ◁ inv (ε_ X Xᘁ)) ≫ (α_ X Xᘁ X).inv ≫ (inv (η_ X Xᘁ) ▷ X)) =
      𝟙 (𝟙_ C ⊗ X) := by
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [← MonoidalCategory.whiskerLeft_comp, IsIso.hom_inv_id,
      MonoidalCategory.whiskerLeft_id]
    simp [Iso.hom_inv_id_assoc, ← comp_whiskerRight]
  rw [h] at cancel
  rw [← cancel_epi ((λ_ X).hom ≫ (ρ_ X).inv), cancel]
  simp

end LeftDualIsoRightDual
end CategoryTheory
