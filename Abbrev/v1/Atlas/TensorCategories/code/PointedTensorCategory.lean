/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PointedTensorCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.TensorCategories.code.ChevalleyProperty.Part2
public import Theorem.Category.Atlas.v1.TensorCategories.code.ChevalleyProperty
public import Theorem.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
public import Theorem.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
public import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
public import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
@[expose] public section

set_option maxHeartbeats 400000

open scoped TensorProduct
open Coalgebra CategoryTheory MonoidalCategory


section PointedTensorCategory

universe v₃ u₃

variable (C : Type u₃) [Category.{v₃} C] [MonoidalCategory C] [Limits.HasZeroMorphisms C]

/-- EGNO Definition 1.28.3: a pointed tensor category, alias for the underlying
`IsPointedTensorCategory` predicate on `C`. -/
abbrev Definition_1_28_3 := _root_.IsPointedTensorCategory C

end PointedTensorCategory
