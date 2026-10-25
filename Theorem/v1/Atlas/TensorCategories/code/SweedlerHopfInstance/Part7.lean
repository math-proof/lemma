/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.SweedlerConcrete
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
import Instance.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part2
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- The Hopf-structure antipode unfolds to `antipodeLM`. -/
@[simp] lemma antipode_is :
    (HopfAlgebraStruct.antipode (R := k) : SweedlerH4 k →ₗ[k] _) = antipodeLM := rfl

end SweedlerH4
