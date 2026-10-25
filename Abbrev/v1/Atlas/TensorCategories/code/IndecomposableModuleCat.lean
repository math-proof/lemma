/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IndecomposableModuleCat.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.DirectSumModuleCategory.Part2
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Class.v1.Atlas.TensorCategories.code.IndecomposableModuleCat
set_option maxHeartbeats 800000

open CategoryTheory

universe u₁ v₁ u₂ v₂


namespace CategoryTheory

/-- Definition 2.4.3: a module category `M` over `C` is indecomposable if it is not equivalent
to a nontrivial direct sum of module categories (with both summands nonzero). -/
abbrev Definition_2_4_3 := @IsIndecomposableModuleCategory

end CategoryTheory
