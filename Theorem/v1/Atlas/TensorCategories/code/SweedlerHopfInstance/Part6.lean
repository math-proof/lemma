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
import Instance.v1.Atlas.TensorCategories.code.SweedlerHopfInstance
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- The coalgebra-structure comultiplication unfolds to `comulLM`. -/
@[simp] lemma comul_is : (CoalgebraStruct.comul : SweedlerH4 k →ₗ[k] _) = comulLM := rfl

/-- The coalgebra-structure counit unfolds to `counitLM`. -/
@[simp] lemma counit_is : (CoalgebraStruct.counit : SweedlerH4 k →ₗ[k] k) = counitLM := rfl

end SweedlerH4
