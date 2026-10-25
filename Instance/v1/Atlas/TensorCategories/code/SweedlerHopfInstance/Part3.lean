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
import Theorem.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part7
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

set_option maxHeartbeats 800000 in
/-- The full `k`-Hopf algebra structure on `SweedlerH4 k`, verifying both antipode axioms
on the basis. -/
noncomputable instance : HopfAlgebra k (SweedlerH4 k) where
  mul_antipode_rTensor_comul := by
    apply linearMap_ext_basis; intro i
    simp only [LinearMap.comp_apply, comul_is, antipode_is, counit_is]
    fin_cases i <;>
      simp [map_add, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
        e_zero_eq_one, e1_mul_e1, e1_mul_e2, e1_mul_e3,
        e2_mul_e1, e3_mul_e1, e3_mul_e2, neg_mul, mul_neg,
        Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
        add_comm, neg_add_cancel, add_neg_cancel]
  mul_antipode_lTensor_comul := by
    apply linearMap_ext_basis; intro i
    simp only [LinearMap.comp_apply, comul_is, antipode_is, counit_is]
    fin_cases i <;>
      simp [map_add, LinearMap.lTensor_tmul, LinearMap.mul'_apply,
        e_zero_eq_one, e1_mul_e1, e1_mul_e2, e1_mul_e3,
        e2_mul_e1, e3_mul_e1, e3_mul_e2, neg_mul, mul_neg,
        Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one,
        add_comm, neg_add_cancel, add_neg_cancel]


end SweedlerH4
