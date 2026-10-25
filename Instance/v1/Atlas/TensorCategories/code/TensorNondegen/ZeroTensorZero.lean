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
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category CategoryTheory.Limits ZeroObject

universe v u


noncomputable section

namespace TensorNondegen

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RigidCategory C] [BraidedCategory C]

/-- The right-tensor functor `- ⊗ Y` in a preadditive monoidal category preserves zero morphisms. -/
instance tensorRight_preservesZeroMorphisms (Y : C) :
    (tensorRight Y).PreservesZeroMorphisms where
  map_zero _ _ := MonoidalPreadditive.zero_whiskerRight

/-- The left-tensor functor `Y ⊗ -` in a preadditive monoidal category preserves zero morphisms. -/
instance tensorLeft_preservesZeroMorphisms (Y : C) :
    (tensorLeft Y).PreservesZeroMorphisms where
  map_zero _ _ := MonoidalPreadditive.whiskerLeft_zero

end TensorNondegen
end
