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
import Def.v1.Atlas.TensorCategories.code.GradedVec.Part5
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


section Rigidity

variable {G : Type u} [Group G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- Each object `X` of `CG G A ω` has an exact pairing with its dual
`Xᘁ = ⟨g⁻¹⟩`, exhibiting `CG G A ω` as a rigid monoidal category. -/
noncomputable instance CG.exactPairing (X : CG G A ω) :
    ExactPairing X (CG.dualObj X) where
  coevaluation' := CG.coevMorphism X
  evaluation' := CG.evalMorphism X
  coevaluation_evaluation' := by
    apply CG.Hom.ext


    show 1 * 1 * ((ω.toFun X.val⁻¹ X.val X.val⁻¹)⁻¹ *
      ((ω.toFun X.val X.val⁻¹ X.val)⁻¹ * 1)) = 1 * 1
    simp only [one_mul, mul_one]
    rw [← mul_inv]
    rw [inv_eq_one]
    have := ω.cocycle_inv_cancel X.val
    rw [mul_comm] at this
    exact this
  evaluation_coevaluation' := by
    apply CG.Hom.ext


    show 1 * 1 * (ω.toFun X.val X.val⁻¹ X.val *
      (1 * (ω.toFun X.val X.val⁻¹ X.val)⁻¹)) = 1 * 1
    simp [mul_inv_cancel]

end Rigidity
