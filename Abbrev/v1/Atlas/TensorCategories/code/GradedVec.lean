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
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part2
set_option maxHeartbeats 800000

open CategoryTheory

universe u v


namespace CG

variable {G : Type u} [Monoid G] {A : Type v} [CommGroup A]

variable {ω : NormalizedGroupCocycle3 G A}

/-- Tensor product of objects in `CG G A ω`: degrees multiply. -/
abbrev tensorObj' (X Y : CG G A ω) : CG G A ω := ⟨X.val * Y.val⟩

/-- Tensor product of morphisms in `CG G A ω`: scalars multiply. -/
abbrev tensorHom' {X₁ X₂ Y₁ Y₂ : CG G A ω} (f : X₁ ⟶ X₂) (f' : Y₁ ⟶ Y₂) :
    tensorObj' X₁ Y₁ ⟶ tensorObj' X₂ Y₂ :=
  ⟨f.val * f'.val, by simp [f.eq, f'.eq]⟩

/-- The monoidal unit object in `CG G A ω` lives in degree `1`. -/
abbrev unit' : CG G A ω := ⟨1⟩

end CG
