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
import Structure.v1.Atlas.TensorCategories.code.GradedVec.Part3
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- Extensionality for `CG.Hom`: morphisms are determined by their
underlying scalar `val`. -/
@[ext]
theorem Hom.ext {X Y : CG G A ω} {f f' : CG.Hom X Y} (hv : f.val = f'.val) : f = f' := by
  cases f; cases f'; congr

end CG
