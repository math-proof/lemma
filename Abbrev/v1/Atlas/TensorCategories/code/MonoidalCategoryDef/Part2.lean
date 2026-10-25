/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/MonoidalCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence
import Def.v1.Atlas.TensorCategories.code.MonoidalCategoryDef
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v v₂ u u₂


namespace TensorCategories

/-- EGNO Definition 1.1.1 (TensorCategories namespace short alias): a monoidal category. -/
abbrev def_1_1_1 (C : Type u) [Category.{v} C] := MonoidalCategory C

/-- EGNO Definition 1.2.6 (TensorCategories namespace): a monoidal category as a sextuple
satisfying the pentagon and triangle axioms. -/
abbrev Definition_1_2_6 (C : Type u) [Category.{v} C] := MonoidalCategory C

/-- EGNO Definition 1.2.6 (TensorCategories namespace short alias). -/
abbrev def_1_2_6 (C : Type u) [Category.{v} C] := MonoidalCategory C

end TensorCategories
