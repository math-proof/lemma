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
import Def.v1.Atlas.TensorCategories.code.GradedVec.Part3
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- The underlying scalar of the left unitor in `CG G A ω` is `1`. -/
@[simp] theorem leftUnitor'_hom_val (X : CG G A ω) :
    (leftUnitor' X).hom.val = 1 := rfl

end CG
