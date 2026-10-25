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
import Theorem.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part3
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- The comultiplication of `H₄` as a `k`-linear map: `1 ↦ 1 ⊗ 1`, `g ↦ g ⊗ g`,
`x ↦ x ⊗ g + 1 ⊗ x`, `gx ↦ gx ⊗ 1 + g ⊗ gx`. -/
noncomputable def comulLM : SweedlerH4 k →ₗ[k] SweedlerH4 k ⊗[k] SweedlerH4 k :=
  lmOfBasis ![
    e 0 ⊗ₜ e 0,
    e 1 ⊗ₜ e 1,
    e 2 ⊗ₜ e 1 + e 0 ⊗ₜ e 2,
    e 3 ⊗ₜ e 0 + e 1 ⊗ₜ e 3
  ]

end SweedlerH4
