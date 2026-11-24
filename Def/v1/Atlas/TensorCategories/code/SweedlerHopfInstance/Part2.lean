module
public import Theorem.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part4
public import Lemma.Category.Atlas.v1.TensorCategories.code.SweedlerConcrete
public import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
public import Theorem.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part2
set_option linter.unusedSimpArgs false
open Coalgebra HopfAlgebra
open scoped TensorProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {k : Type*} [Field k]


namespace SweedlerH4

/-- The counit of `H₄` as a `k`-linear map: `1 ↦ 1`, `g ↦ 1`, `x ↦ 0`, `gx ↦ 0`. -/
noncomputable def counitLM : SweedlerH4 k →ₗ[k] k := lmOfBasis ![1, 1, 0, 0]

end SweedlerH4
