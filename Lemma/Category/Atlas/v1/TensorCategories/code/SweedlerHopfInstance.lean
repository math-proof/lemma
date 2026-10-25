import Mathlib
import sympy.Basic
import Instance.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part4
open Coalgebra HopfAlgebra SweedlerH4
open scoped TensorProduct


namespace SweedlerH4

/--
[e2_mul_e2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma e2_mul_e2
  [Field k] :
-- imply
  (e 2 : SweedlerH4 k) * e 2 = 0 :=
-- proof
  gen_x_sq

end SweedlerH4

namespace SweedlerH4

/--
[e2_mul_e3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma e2_mul_e3
  [Field k] :
-- imply
  (e 2 : SweedlerH4 k) * e 3 = 0 := by
-- proof
  ext m; simp only [coeff_mul, coeff_e, coeff_zero', Fin4_sum, basisMul]; fin_cases m <;> simp

end SweedlerH4

namespace SweedlerH4

/--
[e3_mul_e3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma e3_mul_e3
  [Field k] :
-- imply
  (e 3 : SweedlerH4 k) * e 3 = 0 := by
-- proof
  ext m; simp only [coeff_mul, coeff_e, coeff_zero', Fin4_sum, basisMul]; fin_cases m <;> simp
set_option maxHeartbeats 800000 in

end SweedlerH4

namespace SweedlerH4

/--
[counitLM_mul_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma counitLM_mul_basis
  [Field k]
  {i j : Fin 4} :
-- imply
  counitLM ((e i : SweedlerH4 k) * e j) = counitLM (e i) * counitLM (e j) := by
-- proof
  fin_cases i <;> fin_cases j <;>
    simp [e_zero_eq_one, e1_mul_e1, e1_mul_e2, e1_mul_e3, e2_mul_e1,
      e2_mul_e2, e2_mul_e3, e3_mul_e1, e3_mul_e2, e3_mul_e3]

end SweedlerH4

namespace SweedlerH4

/--
[counitLM_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma counitLM_mul
  [Field k]
  {a b : SweedlerH4 k} :
-- imply
  counitLM (a * b : SweedlerH4 k) = counitLM a * counitLM b := by
-- proof
  conv_lhs => rw [eq_sum_basis a, eq_sum_basis b]
  conv_rhs => rw [eq_sum_basis a, eq_sum_basis b]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, map_smul, smul_eq_mul,
    smul_mul_smul_comm]
  congr 1; ext i; congr 1; ext j
  rw [counitLM_mul_basis]; ring

end SweedlerH4

namespace SweedlerH4

/--
[one_tensor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma one_tensor_eq
  [Field k] :
-- imply
  (1 : SweedlerH4 k ⊗[k] SweedlerH4 k) = e 0 ⊗ₜ e 0 := by
-- proof
  rw [Algebra.TensorProduct.one_def, e_zero_eq_one]

end SweedlerH4

namespace SweedlerH4

/--
[comulLM_mul_e0j](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma comulLM_mul_e0j
  [Field k]
  {j : Fin 4} :
-- imply
  comulLM ((e 0 : SweedlerH4 k) * e j) = comulLM (e 0) * comulLM (e j) := by
-- proof
  simp only [e0_mul, comulLM_e0, ← one_tensor_eq, one_mul]

end SweedlerH4

namespace SweedlerH4

/--
[comulLM_mul_ei0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma comulLM_mul_ei0
  [Field k]
  {i : Fin 4} :
-- imply
  comulLM ((e i : SweedlerH4 k) * e 0) = comulLM (e i) * comulLM (e 0) := by
-- proof
  simp only [mul_e0, comulLM_e0, ← one_tensor_eq, mul_one]
set_option maxHeartbeats 800000 in

end SweedlerH4

namespace SweedlerH4

/--
[comulLM_mul_e11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma comulLM_mul_e11
  [Field k] :
-- imply
  comulLM ((e 1 : SweedlerH4 k) * e 1) = comulLM (e 1) * comulLM (e 1) := by
-- proof
  simp [e1_mul_e1, e_zero_eq_one, Algebra.TensorProduct.tmul_mul_tmul]
set_option maxHeartbeats 800000 in

end SweedlerH4

namespace SweedlerH4

/--
[comulLM_mul_e12](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma comulLM_mul_e12
  [Field k] :
-- imply
  comulLM ((e 1 : SweedlerH4 k) * e 2) = comulLM (e 1) * comulLM (e 2) := by
-- proof
  simp only [e1_mul_e2, comulLM_e3, comulLM_e1, comulLM_e2, comulLM_e0, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, e1_mul_e1, e_zero_eq_one,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, mul_one, one_mul]
set_option maxHeartbeats 800000 in

end SweedlerH4

namespace SweedlerH4

/--
[comulLM_mul_e13](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma comulLM_mul_e13
  [Field k] :
-- imply
  comulLM ((e 1 : SweedlerH4 k) * e 3) = comulLM (e 1) * comulLM (e 3) := by
-- proof
  simp only [e1_mul_e3, comulLM_e2, comulLM_e1, comulLM_e3, comulLM_e0, mul_add,
    Algebra.TensorProduct.tmul_mul_tmul, e1_mul_e1, e_zero_eq_one,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, mul_one, one_mul]
set_option maxHeartbeats 800000 in

end SweedlerH4

namespace SweedlerH4

/--
[comulLM_mul_e21](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma comulLM_mul_e21
  [Field k] :
-- imply
  comulLM ((e 2 : SweedlerH4 k) * e 1) = comulLM (e 2) * comulLM (e 1) := by
-- proof
  simp only [e2_mul_e1, map_neg, comulLM_e3, comulLM_e2, comulLM_e1, comulLM_e0, add_mul,
    Algebra.TensorProduct.tmul_mul_tmul, e2_mul_e1, e1_mul_e1, e_zero_eq_one,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, mul_one, one_mul]
  abel
set_option maxHeartbeats 800000 in

end SweedlerH4

namespace SweedlerH4

/--
[comulLM_mul_e23](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma comulLM_mul_e23
  [Field k] :
-- imply
  comulLM ((e 2 : SweedlerH4 k) * e 3) = comulLM (e 2) * comulLM (e 3) := by
-- proof
  simp only [e2_mul_e3, map_zero, comulLM_e2, comulLM_e0, comulLM_e1, comulLM_e3,
    add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    e2_mul_e1, e2_mul_e2, e2_mul_e3, e1_mul_e3,
    e_zero_eq_one, TensorProduct.tmul_zero, TensorProduct.zero_tmul,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, add_zero, zero_add,
    neg_add_cancel, add_neg_cancel, neg_zero, mul_one, one_mul]
set_option maxHeartbeats 800000 in

end SweedlerH4

namespace SweedlerH4

/--
[comulLM_mul_e31](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma comulLM_mul_e31
  [Field k] :
-- imply
  comulLM ((e 3 : SweedlerH4 k) * e 1) = comulLM (e 3) * comulLM (e 1) := by
-- proof
  simp only [e3_mul_e1, map_neg, comulLM_e2, comulLM_e3, comulLM_e0, comulLM_e1,
    add_mul, Algebra.TensorProduct.tmul_mul_tmul,
    e3_mul_e1, e1_mul_e1, e_zero_eq_one,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, mul_one, one_mul]
  abel
set_option maxHeartbeats 800000 in

end SweedlerH4

namespace SweedlerH4

/--
[comulLM_mul_e32](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma comulLM_mul_e32
  [Field k] :
-- imply
  comulLM ((e 3 : SweedlerH4 k) * e 2) = comulLM (e 3) * comulLM (e 2) := by
-- proof
  simp only [e3_mul_e2, map_zero, comulLM_e3, comulLM_e0, comulLM_e1, comulLM_e2,
    add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    e3_mul_e1, e3_mul_e2, e1_mul_e2,
    e_zero_eq_one, TensorProduct.tmul_zero, TensorProduct.zero_tmul,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, add_zero, zero_add,
    neg_add_cancel, add_neg_cancel, neg_zero, mul_one, one_mul]
set_option maxHeartbeats 800000 in

end SweedlerH4

namespace SweedlerH4

/--
[comulLM_mul_e33](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
lemma comulLM_mul_e33
  [Field k] :
-- imply
  comulLM ((e 3 : SweedlerH4 k) * e 3) = comulLM (e 3) * comulLM (e 3) := by
-- proof
  simp only [e3_mul_e3, map_zero, comulLM_e3, comulLM_e0, comulLM_e1, comulLM_e2,
    add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
    e3_mul_e1, e1_mul_e3, e3_mul_e3, e3_mul_e2,
    e_zero_eq_one, TensorProduct.tmul_zero, TensorProduct.zero_tmul,
    TensorProduct.neg_tmul, TensorProduct.tmul_neg, add_zero, zero_add,
    neg_add_cancel, add_neg_cancel, neg_zero, mul_one, one_mul]

end SweedlerH4

/--
[eq_sum_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma eq_sum_basis_eq
  [Field k]
  {a : SweedlerH4 k} :
-- imply
  a = ∑ i : Fin 4, a.coeff i • e i := by
-- proof
  apply SweedlerH4.eq_sum_basis a

/--
[linearMap_ext_basis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma linearMap_ext_basis_eq
  [Field k]
  [AddCommMonoid M]
  [Module k M]
  {f g : SweedlerH4 k →ₗ[k] M}
-- given
  (h : ∀ i : Fin 4, f (e i) = g (e i)) :
-- imply
  f = g := by
-- proof
  apply SweedlerH4.linearMap_ext_basis h

/--
[lmOfBasis_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma lmOfBasis_e_eq
  [Field k]
  [AddCommMonoid M]
  [Module k M]
  {v : Fin 4 → M}
  {i : Fin 4} :
-- imply
  lmOfBasis v (e i : SweedlerH4 k) = v i := by
-- proof
  apply SweedlerH4.lmOfBasis_e v i

/--
[counitLM_e](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma counitLM_e_eq
  [Field k]
  {i : Fin 4} :
-- imply
  counitLM (e i : SweedlerH4 k) = ![1, 1, 0, 0] i := by
-- proof
  apply SweedlerH4.counitLM_e i

/--
[counitLM_e0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma counitLM_e0_eq
  [Field k] :
-- imply
  counitLM (e 0 : SweedlerH4 k) = 1 := by
-- proof
  apply SweedlerH4.counitLM_e0

/--
[counitLM_e1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma counitLM_e1_eq
  [Field k] :
-- imply
  counitLM (e 1 : SweedlerH4 k) = 1 := by
-- proof
  apply SweedlerH4.counitLM_e1

/--
[counitLM_e2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma counitLM_e2_eq
  [Field k] :
-- imply
  counitLM (e 2 : SweedlerH4 k) = 0 := by
-- proof
  apply SweedlerH4.counitLM_e2

/--
[counitLM_e3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma counitLM_e3_eq
  [Field k] :
-- imply
  counitLM (e 3 : SweedlerH4 k) = 0 := by
-- proof
  apply SweedlerH4.counitLM_e3

/--
[counitLM_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma counitLM_one_eq
  [Field k] :
-- imply
  counitLM (1 : SweedlerH4 k) = 1 := by
-- proof
  apply SweedlerH4.counitLM_one

/--
[comulLM_e0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma comulLM_e0_eq
  [Field k] :
-- imply
  comulLM (e 0 : SweedlerH4 k) = e 0 ⊗ₜ e 0 := by
-- proof
  apply SweedlerH4.comulLM_e0

/--
[comulLM_e1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma comulLM_e1_eq
  [Field k] :
-- imply
  comulLM (e 1 : SweedlerH4 k) = e 1 ⊗ₜ e 1 := by
-- proof
  apply SweedlerH4.comulLM_e1

/--
[comulLM_e2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma comulLM_e2_eq
  [Field k] :
-- imply
  comulLM (e 2 : SweedlerH4 k) = e 2 ⊗ₜ e 1 + e 0 ⊗ₜ e 2 := by
-- proof
  apply SweedlerH4.comulLM_e2

/--
[comulLM_e3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma comulLM_e3_eq
  [Field k] :
-- imply
  comulLM (e 3 : SweedlerH4 k) = e 3 ⊗ₜ e 0 + e 1 ⊗ₜ e 3 := by
-- proof
  apply SweedlerH4.comulLM_e3

/--
[comulLM_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma comulLM_one_eq
  [Field k] :
-- imply
  comulLM (1 : SweedlerH4 k) = e 0 ⊗ₜ e 0 := by
-- proof
  apply SweedlerH4.comulLM_one

/--
[antipodeLM_e0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma antipodeLM_e0_eq
  [Field k] :
-- imply
  antipodeLM (e 0 : SweedlerH4 k) = e 0 := by
-- proof
  apply SweedlerH4.antipodeLM_e0

/--
[antipodeLM_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma antipodeLM_one_eq
  [Field k] :
-- imply
  antipodeLM (1 : SweedlerH4 k) = 1 := by
-- proof
  apply SweedlerH4.antipodeLM_one

/--
[antipodeLM_e1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma antipodeLM_e1_eq
  [Field k] :
-- imply
  antipodeLM (e 1 : SweedlerH4 k) = e 1 := by
-- proof
  apply SweedlerH4.antipodeLM_e1

/--
[antipodeLM_e2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma antipodeLM_e2_eq
  [Field k] :
-- imply
  antipodeLM (e 2 : SweedlerH4 k) = e 3 := by
-- proof
  apply SweedlerH4.antipodeLM_e2

/--
[antipodeLM_e3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma antipodeLM_e3_eq
  [Field k] :
-- imply
  antipodeLM (e 3 : SweedlerH4 k) = -(e 2) := by
-- proof
  apply SweedlerH4.antipodeLM_e3

/--
[e0_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma e0_mul_eq
  [Field k]
  {a : SweedlerH4 k} :
-- imply
  e 0 * a = a := by
-- proof
  apply SweedlerH4.e0_mul a

/--
[mul_e0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma mul_e0_eq
  [Field k]
  {a : SweedlerH4 k} :
-- imply
  a * e 0 = a := by
-- proof
  apply SweedlerH4.mul_e0 a

/--
[e1_mul_e1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma e1_mul_e1_eq
  [Field k] :
-- imply
  (e 1 : SweedlerH4 k) * e 1 = e 0 := by
-- proof
  apply SweedlerH4.e1_mul_e1

/--
[e1_mul_e2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma e1_mul_e2_eq
  [Field k] :
-- imply
  (e 1 : SweedlerH4 k) * e 2 = e 3 := by
-- proof
  apply SweedlerH4.e1_mul_e2

/--
[e1_mul_e3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma e1_mul_e3_eq
  [Field k] :
-- imply
  (e 1 : SweedlerH4 k) * e 3 = e 2 := by
-- proof
  apply SweedlerH4.e1_mul_e3

/--
[e2_mul_e1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma e2_mul_e1_eq
  [Field k] :
-- imply
  (e 2 : SweedlerH4 k) * e 1 = -(e 3) := by
-- proof
  apply SweedlerH4.e2_mul_e1

/--
[e3_mul_e1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma e3_mul_e1_eq
  [Field k] :
-- imply
  (e 3 : SweedlerH4 k) * e 1 = -(e 2) := by
-- proof
  apply SweedlerH4.e3_mul_e1

/--
[e3_mul_e2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma e3_mul_e2_eq
  [Field k] :
-- imply
  (e 3 : SweedlerH4 k) * e 2 = 0 := by
-- proof
  apply SweedlerH4.e3_mul_e2

/--
[comul_is](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma comul_is_eq
  [Field k] :
-- imply
  (CoalgebraStruct.comul : SweedlerH4 k →ₗ[k] _) = comulLM := by
-- proof
  apply SweedlerH4.comul_is

/--
[counit_is](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma counit_is_eq
  [Field k] :
-- imply
  (CoalgebraStruct.counit : SweedlerH4 k →ₗ[k] k) = counitLM := by
-- proof
  apply SweedlerH4.counit_is

/--
[antipode_is](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma antipode_is_eq
  [Field k] :
-- imply
  (HopfAlgebraStruct.antipode (R := k) : SweedlerH4 k →ₗ[k] _) = antipodeLM := by
-- proof
  apply SweedlerH4.antipode_is

/--
[comul_gen_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma comul_gen_g_eq
  [Field k] :
-- imply
  (Coalgebra.comul (R := k)) (gen_g : SweedlerH4 k) = (gen_g : SweedlerH4 k) ⊗ₜ gen_g := by
-- proof
  apply SweedlerH4.comul_gen_g

/--
[comul_gen_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma comul_gen_x_eq
  [Field k] :
-- imply
  (Coalgebra.comul (R := k)) (gen_x : SweedlerH4 k) = (gen_x : SweedlerH4 k) ⊗ₜ gen_g + (1 : SweedlerH4 k) ⊗ₜ gen_x := by
-- proof
  apply SweedlerH4.comul_gen_x

/--
[counit_gen_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma counit_gen_g_eq
  [Field k] :
-- imply
  (Coalgebra.counit (R := k)) (gen_g : SweedlerH4 k) = (1 : k) := by
-- proof
  apply SweedlerH4.counit_gen_g

/--
[counit_gen_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma counit_gen_x_eq
  [Field k] :
-- imply
  (Coalgebra.counit (R := k)) (gen_x : SweedlerH4 k) = (0 : k) := by
-- proof
  apply SweedlerH4.counit_gen_x

/--
[antipode_gen_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma antipode_gen_g_eq
  [Field k] :
-- imply
  (HopfAlgebra.antipode k) (gen_g : SweedlerH4 k) = gen_g := by
-- proof
  apply SweedlerH4.antipode_gen_g

/--
[antipode_gen_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean)
-/
@[path]
private lemma antipode_gen_x_eq
  [Field k] :
-- imply
  (HopfAlgebra.antipode k) (gen_x : SweedlerH4 k) = (gen_g : SweedlerH4 k) * gen_x := by
-- proof
  apply SweedlerH4.antipode_gen_x


-- created on 2026-10-23
