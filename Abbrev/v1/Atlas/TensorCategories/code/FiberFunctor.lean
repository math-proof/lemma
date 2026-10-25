/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiberFunctor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
import Lemma.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor
open CategoryTheory MonoidalCategory

universe v u w


namespace TensorCategories

/-- Definition 1.21 (EGNO): A fiber functor on a category `C` is a (quasi-)tensor
functor `C ⥤ ModuleCat k` that is exact and faithful. -/
abbrev FiberFunctor_1_21 := @FiberFunctor

end TensorCategories
