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
import Theorem.v1.Atlas.TensorCategories.code.GradedVec
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- Category instance on `CG G A ω`: composition multiplies the
underlying scalars and identity morphisms have scalar `1`. -/
instance instCategory : Category (CG G A ω) where
  Hom := CG.Hom
  id _ := ⟨1, rfl⟩
  comp f f' := ⟨f.val * f'.val, f.eq.trans f'.eq⟩
  id_comp _ := Hom.ext (one_mul _)
  comp_id _ := Hom.ext (mul_one _)
  assoc _ _ _ := Hom.ext (mul_assoc _ _ _)


end CG
