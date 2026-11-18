/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GradedVec.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Tactic.Group
public import Def.v1.Atlas.TensorCategories.code.GradedVec.Part4

@[expose] public section
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- The underlying scalar of the right unitor in `CG G A ω` is `1`. -/
@[simp] public theorem rightUnitor'_hom_val (X : CG G A ω) :
    (rightUnitor' X).hom.val = 1 := rfl

end CG
