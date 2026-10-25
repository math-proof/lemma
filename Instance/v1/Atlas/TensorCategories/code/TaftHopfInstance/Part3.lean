/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.TaftConcrete.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.TaftConcrete
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
import Theorem.v1.Atlas.TensorCategories.code.TaftHopfInstance.Part3
open Coalgebra HopfAlgebra
open scoped TensorProduct


namespace TaftAlgebraType

variable (k : Type*) [Field k] (n : ℕ) [NeZero n] (q : k) [Fact (q ^ n = 1)]


local notation "A" => TaftAlgebraType n q k

variable [TaftHopfData k n q]

noncomputable section

/-- The Taft algebra is a Hopf algebra over `k`. -/
noncomputable instance taftHopfAlgebra [TaftHopfData k n q] :
    HopfAlgebra k A where
  mul_antipode_rTensor_comul := taft_hopf_rTensor k n q
  mul_antipode_lTensor_comul := taft_hopf_lTensor k n q

/-- The Taft algebra `TaftAlgebraType n q k` realises the abstract `TaftAlgebra` structure
on `(k, A)` with the concrete generators `g, x` and the antipode, comultiplication, counit
formulas extracted from `TaftHopfData`. -/
noncomputable instance taftAlgebraInstance [inst : TaftHopfData k n q] :
    TaftAlgebra k (TaftAlgebraType n q k) where
  n := n
  hn := inst.hn2
  q := q
  hq := inst.hq_prim
  g := gen_g (k := k) (q := q) inst.hn2
  x := gen_x (k := k) (q := q) inst.hn2
  g_pow_n := inst.gen_g_pow_n
  x_pow_n := inst.gen_x_pow_n
  gx_comm := inst.gen_gx_comm
  comul_g := by
    show taftComulLM k n q (gen_g inst.hn2) = _
    exact taft_comul_gen_g k n q
  comul_x := by
    show taftComulLM k n q (gen_x inst.hn2) = _
    exact taft_comul_gen_x k n q
  counit_g := by
    show taftCounitLM k n q (gen_g inst.hn2) = _
    exact taft_counit_gen_g k n q
  counit_x := by
    show taftCounitLM k n q (gen_x inst.hn2) = _
    exact taft_counit_gen_x k n q
  antipode_g := by
    show taftAntipodeLM k n q (gen_g inst.hn2) = _
    exact taft_antipode_gen_g k n q
  antipode_x := by
    show taftAntipodeLM k n q (gen_x inst.hn2) = _
    exact taft_antipode_gen_x k n q
  finrank_eq := by rw [finrank_eq]; ring

end
end TaftAlgebraType
