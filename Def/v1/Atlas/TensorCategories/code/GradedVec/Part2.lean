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
import Abbrev.v1.Atlas.TensorCategories.code.GradedVec
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- The associator in the twisted category `CG G A ω`, with structure
constant `ω(X.val, Y.val, Z.val)` on each component. -/
def twistedAssociator' (X Y Z : CG G A ω) :
    tensorObj' (tensorObj' X Y) Z ≅ tensorObj' X (tensorObj' Y Z) where
  hom := ⟨ω.toFun X.val Y.val Z.val, by simp [mul_assoc]⟩
  inv := ⟨(ω.toFun X.val Y.val Z.val)⁻¹, by simp [mul_assoc]⟩
  hom_inv_id := Hom.ext (mul_inv_cancel _)
  inv_hom_id := Hom.ext (inv_mul_cancel _)

end CG
