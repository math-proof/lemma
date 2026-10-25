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
import Theorem.v1.Atlas.TensorCategories.code.SweedlerHopfInstance
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- Build a `k`-linear map `SweedlerH4 k →ₗ[k] M` by prescribing its values on the four basis
vectors `e 0, e 1, e 2, e 3`. -/
noncomputable def lmOfBasis {M : Type*} [AddCommMonoid M] [Module k M]
    (v : Fin 4 → M) : SweedlerH4 k →ₗ[k] M where
  toFun a := ∑ i : Fin 4, a.coeff i • v i
  map_add' a b := by simp [coeff_add, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp [coeff_smul, smul_eq_mul, Finset.smul_sum, smul_smul]

end SweedlerH4
