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
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- Every element of `SweedlerH4 k` is the sum of its coefficients times the standard basis
vectors `e i`. -/
lemma eq_sum_basis (a : SweedlerH4 k) : a = ∑ i : Fin 4, a.coeff i • e i := by
  ext m
  rw [show ∑ i : Fin 4, a.coeff i • e i =
    a.coeff 0 • e 0 + a.coeff 1 • e 1 + a.coeff 2 • e 2 + a.coeff 3 • (e 3 : SweedlerH4 k)
    from Fin.sum_univ_four _]
  simp only [coeff_add, coeff_smul, coeff_e]
  fin_cases m <;> simp

/-- Two `k`-linear maps out of `SweedlerH4 k` agree as soon as they agree on each of the four
basis vectors `e i`. -/
lemma linearMap_ext_basis {M : Type*} [AddCommMonoid M] [Module k M]
    {f g : SweedlerH4 k →ₗ[k] M} (h : ∀ i : Fin 4, f (e i) = g (e i)) :
    f = g := by
  ext a; rw [eq_sum_basis a]; simp_rw [map_sum, map_smul]
  congr 1; ext i; rw [h i]

end SweedlerH4
