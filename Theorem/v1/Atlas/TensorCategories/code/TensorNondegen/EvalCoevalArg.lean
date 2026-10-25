/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TensorNondegen/EvalCoevalArg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.UnitSemisimplicity.EvalCoeval
import Lemma.Category.Atlas.v1.TensorCategories.code.UnitSemisimplicity.EvalCoeval
open CategoryTheory MonoidalCategory Category CategoryTheory.Limits

universe v u


noncomputable section

namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [RigidCategory C]

end TensorCategories
end
