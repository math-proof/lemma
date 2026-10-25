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
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part4
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- Right unit isomorphism `X ⊗ 1 ≅ X` in `CG G A ω`. -/
def rightUnitor' (X : CG G A ω) : tensorObj' X unit' ≅ X where
  hom := ⟨1, by simp⟩
  inv := ⟨1, by simp⟩
  hom_inv_id := Hom.ext (mul_one _)
  inv_hom_id := Hom.ext (mul_one _)

end CG
