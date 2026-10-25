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
import Def.v1.Atlas.TensorCategories.code.GradedVec.Part2
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- The forward scalar of the twisted associator is `ω(X, Y, Z)`. -/
@[simp] theorem twistedAssociator'_hom_val (X Y Z : CG G A ω) :
    (twistedAssociator' X Y Z).hom.val = ω.toFun X.val Y.val Z.val := rfl

/-- The inverse scalar of the twisted associator is `ω(X, Y, Z)⁻¹`. -/
@[simp] theorem twistedAssociator'_inv_val (X Y Z : CG G A ω) :
    (twistedAssociator' X Y Z).inv.val = (ω.toFun X.val Y.val Z.val)⁻¹ := rfl

end CG
