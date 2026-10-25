/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Lemma_1_51_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Class.v1.Atlas.TensorCategories.code.Lemma_1_51_1
open CategoryTheory MonoidalCategory Category

universe v u


namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

variable [RigidCategory C]

/-- The double right dual `X**` of an object `X` in a rigid monoidal category, used in
Section 1.51 of EGNO. -/
def doubleDual_1_51 (X : C) : C :=
  HasRightDual.rightDual (HasRightDual.rightDual X)

end CategoryTheory
