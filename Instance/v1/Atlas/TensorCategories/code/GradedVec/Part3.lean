/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.Tactic.Group
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part5
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- Monoidal-category structure data on `CG G A ω`: tensor product,
unit, associator, and unitors as defined above. -/
instance monoidalCategoryStruct : MonoidalCategoryStruct (CG G A ω) where
  tensorObj := tensorObj'
  whiskerLeft X _ _ f := tensorHom' (𝟙 X) f
  whiskerRight f Y := tensorHom' f (𝟙 Y)
  tensorHom := tensorHom'
  tensorUnit := unit'
  associator := twistedAssociator'
  leftUnitor := leftUnitor'
  rightUnitor := rightUnitor'

/-- `CG G A ω` is a monoidal category: the pentagon axiom follows from
the cocycle identity of `ω` and the triangle axiom from normalisation.
This is the construction of `Vec_G^ω` (EGNO §1.7). -/
instance monoidalCategory : MonoidalCategory (CG G A ω) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun _ _ => Hom.ext (show (1 : A) * 1 = 1 from by simp))
    (id_tensorHom := fun _ {_ _} _ => rfl)
    (tensorHom_id := fun _ _ => rfl)
    (tensorHom_comp_tensorHom := fun f₁ f₂ g₁ g₂ => Hom.ext (by
      show f₁.val * f₂.val * (g₁.val * g₂.val) = (f₁.val * g₁.val) * (f₂.val * g₂.val)
      simp [mul_comm, mul_left_comm]))
    (associator_naturality := fun f₁ f₂ f₃ => Hom.ext (by
      show (f₁.val * f₂.val) * f₃.val * ω.toFun _ _ _ =
           ω.toFun _ _ _ * (f₁.val * (f₂.val * f₃.val))
      rw [f₁.eq, f₂.eq, f₃.eq]; simp [mul_comm, mul_left_comm]))
    (leftUnitor_naturality := fun f => Hom.ext (by
      show 1 * f.val * 1 = 1 * f.val; simp))
    (rightUnitor_naturality := fun f => Hom.ext (by
      show f.val * 1 * 1 = 1 * f.val; simp))
    (pentagon := fun W X Y Z => Hom.ext (by
      show ω.toFun W.val X.val Y.val * 1 *
           (ω.toFun W.val (X.val * Y.val) Z.val *
           (1 * ω.toFun X.val Y.val Z.val)) =
           ω.toFun (W.val * X.val) Y.val Z.val *
           ω.toFun W.val X.val (Y.val * Z.val)
      simp only [mul_one, one_mul]
      have h := (ω.cocycle_cond W.val X.val Y.val Z.val).symm
      rw [mul_assoc] at h; exact h))
    (triangle := fun X Y => Hom.ext (by
      show ω.toFun X.val 1 Y.val * (1 * 1) = 1 * 1; simp [ω.normalized]))

end CG
