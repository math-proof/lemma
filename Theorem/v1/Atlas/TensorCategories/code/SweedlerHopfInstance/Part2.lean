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
import Def.v1.Atlas.TensorCategories.code.SweedlerHopfInstance
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- A linear map built via `lmOfBasis` evaluates to its prescribed value on each basis vector. -/
@[simp] lemma lmOfBasis_e {M : Type*} [AddCommMonoid M] [Module k M]
    (v : Fin 4 → M) (i : Fin 4) : lmOfBasis v (e i : SweedlerH4 k) = v i := by
  simp only [lmOfBasis, LinearMap.coe_mk, AddHom.coe_mk, coeff_e, Fin4_sum]
  fin_cases i <;> simp

end SweedlerH4
