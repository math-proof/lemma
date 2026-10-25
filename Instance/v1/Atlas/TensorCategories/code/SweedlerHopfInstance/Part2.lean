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
import Theorem.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part6
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

set_option maxHeartbeats 800000 in
/-- The full `k`-coalgebra structure on `SweedlerH4 k`, verifying coassociativity and the
counit axioms on the basis. -/
noncomputable instance : Coalgebra k (SweedlerH4 k) where
  coassoc := by
    apply linearMap_ext_basis; intro i
    simp only [LinearMap.comp_apply, comul_is]
    fin_cases i <;>
      simp [map_add, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        TensorProduct.assoc_tmul, TensorProduct.add_tmul, TensorProduct.tmul_add,
        add_assoc]
  rTensor_counit_comp_comul := by
    apply linearMap_ext_basis; intro i
    simp only [LinearMap.comp_apply, comul_is, counit_is]
    fin_cases i <;>
      simp [map_add, LinearMap.rTensor_tmul, TensorProduct.mk_apply]
  lTensor_counit_comp_comul := by
    apply linearMap_ext_basis; intro i
    simp only [LinearMap.comp_apply, comul_is, counit_is]
    fin_cases i <;>
      simp [map_add, LinearMap.lTensor_tmul,
        TensorProduct.mk_apply, LinearMap.flip_apply]


/-- `SweedlerH4 k` is a `k`-bialgebra: counit and comultiplication are both algebra
homomorphisms. -/
noncomputable instance : HopfAlgebraStruct k (SweedlerH4 k) where
  antipode := antipodeLM

end SweedlerH4
