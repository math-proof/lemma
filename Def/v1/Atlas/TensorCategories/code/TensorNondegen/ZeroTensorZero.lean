/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorNondegen/ZeroTensorZero.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Theorem.v1.Atlas.TensorCategories.code.TensorNondegen.ZeroTensorZero
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits ZeroObject

universe v u


noncomputable section

namespace TensorNondegen

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]

/-- Corollary: an object whose tensor square is isomorphic to the zero object is itself
isomorphic to zero. -/
def iso_zero_of_tensorSelf_iso_zero (X : C) (e : X ⊗ X ≅ (0 : C)) : X ≅ (0 : C) :=
  (isZero_of_tensorSelf_isZero X (e.isZero_iff.mpr (isZero_zero C))).iso (isZero_zero C)

end TensorNondegen
end
