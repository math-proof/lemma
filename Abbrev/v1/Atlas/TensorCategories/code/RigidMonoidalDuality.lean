/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RigidMonoidalDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Functor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits MonoidalOpposite Opposite

universe v u


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]


/-- Definition 1.10.1 (alias): an object `X` has a right dual. -/
abbrev Definition_1_10_1 (X : C) := HasRightDual X

/-- Definition 1.10.1 (named right dual): an object `X` has a right dual. -/
abbrev Definition_1_10_1_RightDual (X : C) := HasRightDual X

/-- Companion to Definition 1.10.1: an object `X` has a left dual. -/
abbrev def_1_10_1_LeftDual (X : C) := HasLeftDual X


/-- Definition 1.10.2: an object `X` has a left dual. -/
abbrev Definition_1_10_2 (X : C) := HasLeftDual X


end TensorCategories
