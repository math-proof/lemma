/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/PointedTensorCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.TensorCategories.code.ChevalleyProperty.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.ChevalleyProperty
import Lemma.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
import Lemma.Category.Atlas.v1.TensorCategories.code.FiniteTensorCategory
import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
import Instance.v1.Atlas.TensorCategories.code.FiniteTensorCategory.Part8
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
