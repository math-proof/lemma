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
import Instance.v1.Atlas.TensorCategories.code.GradedVec.Part2
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- Underlying scalar of the composition of morphisms in `CG G A ω`. -/
@[simp] theorem comp_val {X Y Z : CG G A ω} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = f.val * g.val := rfl

/-- The underlying scalar of the identity morphism is `1`. -/
@[simp] theorem id_val (X : CG G A ω) : (𝟙 X : X ⟶ X).val = 1 := rfl

end CG
