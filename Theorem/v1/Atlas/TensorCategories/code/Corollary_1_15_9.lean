/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Corollary_1_15_9.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
open CategoryTheory MonoidalCategory Limits

universe u v


section Corollary_1_15_9

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RightRigidCategory C]

end Corollary_1_15_9
