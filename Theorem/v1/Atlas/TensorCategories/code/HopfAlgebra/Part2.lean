/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module
import Def.v1.Atlas.TensorCategories.code.HopfAlgebra.Part2
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra WithConv LinearMap
open scoped TensorProduct

universe u v


section Proposition_1_22_1

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [HopfAlgebra R A]

/-- Evaluation of `antimulComm` on a pure tensor: `(a ⊗ b) ↦ S(a) * S(b)`. -/
@[simp]
lemma HopfAlgebra.antimulComm_tmul (a b : A) :
    HopfAlgebra.antimulComm (a ⊗ₜ[R] b) = antipode R a * antipode R b := by
  simp [antimulComm, Algebra.TensorProduct.lmul'_apply_tmul]

/-- Composing `lmul'` with `id ⊗ id` recovers the ordinary multiplication map `μ`. -/
lemma lmul'_comp_map_id : (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toLinearMap.comp
    (TensorProduct.map (.id : A →ₗ[R] A) .id) = mul' R A := by
  ext a b; simp [Algebra.TensorProduct.lmul'_apply_tmul, mul'_apply]

/-- Composing `lmul'` with `(η ∘ ε) ⊗ (η ∘ ε)` recovers the unit-times-counit map on
`A ⊗ A`, i.e. `η ∘ (ε ⊗ ε)`. -/
lemma lmul'_comp_unit_tensor_unit :
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toLinearMap.comp
      (TensorProduct.map (Algebra.linearMap R A ∘ₗ counit) (Algebra.linearMap R A ∘ₗ counit)) =
    Algebra.linearMap R A ∘ₗ (counit : A ⊗[R] A →ₗ[R] R) := by
  ext a b
  simp [Algebra.TensorProduct.lmul'_apply_tmul, TensorProduct.counit_tmul,
        Algebra.algebraMap_eq_smul_one]
  rw [smul_smul, mul_comm]

/-- In the commutative case, `antimulComm` is a right convolution inverse of `μ` as maps
`A ⊗ A → A`. -/
theorem HopfAlgebra.antimulComm_conv_mul :
    (toConv HopfAlgebra.antimulComm : WithConv (A ⊗[R] A →ₗ[R] A)) * toConv (mul' R A) = 1 := by
  have h1 := algHom_comp_convMul_distrib (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A)
    (toConv (TensorProduct.map (antipode R) (antipode R) : (A ⊗[R] A) →ₗ[R] (A ⊗[R] A)))
    (toConv (TensorProduct.map (.id : A →ₗ[R] A) .id))
  have h2 : toConv (TensorProduct.map (antipode R) (antipode R) : (A ⊗[R] A) →ₗ[R] (A ⊗[R] A)) *
      toConv (TensorProduct.map (.id : A →ₗ[R] A) .id) =
      toConv (TensorProduct.map
        (toConv (antipode R) * toConv (.id : A →ₗ[R] A) : WithConv (A →ₗ[R] A)).ofConv
        ((toConv (antipode R) * toConv (.id : A →ₗ[R] A) : WithConv (A →ₗ[R] A)).ofConv)) :=
    TensorProduct.map_convMul_map
  rw [HopfAlgebra.antipode_conv_id] at h2
  rw [h2] at h1
  rw [LinearMap.convOne_def] at h1
  rw [lmul'_comp_unit_tensor_unit, lmul'_comp_map_id] at h1
  have key : toConv (Algebra.linearMap R A ∘ₗ (counit : A ⊗[R] A →ₗ[R] R)) =
      toConv HopfAlgebra.antimulComm * toConv (mul' R A) := by
    have := congr_arg toConv h1
    rw [toConv_ofConv] at this
    exact this
  rw [← key, ← LinearMap.convOne_def]

/-- In the commutative case, `antimulComm` is a left convolution inverse of `μ` as maps
`A ⊗ A → A`. -/
theorem HopfAlgebra.mul_conv_antimulComm :
    (toConv (mul' R A) : WithConv (A ⊗[R] A →ₗ[R] A)) *
    toConv HopfAlgebra.antimulComm = 1 := by
  have h1 := algHom_comp_convMul_distrib (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A)
    (toConv (TensorProduct.map (.id : A →ₗ[R] A) .id))
    (toConv (TensorProduct.map (antipode R) (antipode R) : (A ⊗[R] A) →ₗ[R] (A ⊗[R] A)))
  have h2 : toConv (TensorProduct.map (.id : A →ₗ[R] A) .id) *
      toConv (TensorProduct.map (antipode R) (antipode R) : (A ⊗[R] A) →ₗ[R] (A ⊗[R] A)) =
      toConv (TensorProduct.map
        (toConv (.id : A →ₗ[R] A) * toConv (antipode R) : WithConv (A →ₗ[R] A)).ofConv
        ((toConv (.id : A →ₗ[R] A) * toConv (antipode R) : WithConv (A →ₗ[R] A)).ofConv)) :=
    TensorProduct.map_convMul_map
  rw [HopfAlgebra.id_conv_antipode] at h2
  rw [h2] at h1
  rw [LinearMap.convOne_def] at h1
  rw [lmul'_comp_unit_tensor_unit, lmul'_comp_map_id (R := R) (A := A)] at h1
  have key : toConv (Algebra.linearMap R A ∘ₗ (counit : A ⊗[R] A →ₗ[R] R)) =
      toConv (mul' R A) * toConv HopfAlgebra.antimulComm := by
    have := congr_arg toConv h1
    rw [toConv_ofConv] at this
    exact this
  rw [← key, ← LinearMap.convOne_def]

/-- The composite `S ∘ μ` is a right convolution inverse of `μ` in the commutative case. -/
theorem HopfAlgebra.Smul_conv_mul :
    (toConv ((antipode R).comp (mul' R A)) : WithConv (A ⊗[R] A →ₗ[R] A)) *
    toConv (mul' R A) = 1 := by
  have key : ∀ (a b : A),
      (mul' R A) (TensorProduct.map ((antipode R).comp (mul' R A)) (mul' R A)
        (comul (a ⊗ₜ[R] b))) =
      algebraMap R A (counit (a ⊗ₜ[R] b)) := by
    intro a b
    obtain ⟨sa, hsa⟩ := TensorProduct.exists_finset (R := R) (M := A) (N := A) (comul (R := R) a)
    obtain ⟨sb, hsb⟩ := TensorProduct.exists_finset (R := R) (M := A) (N := A) (comul (R := R) b)
    rw [TensorProduct.comul_def, comp_apply, TensorProduct.AlgebraTensorModule.map_tmul, hsa, hsb]
    simp only [TensorProduct.tmul_sum, TensorProduct.sum_tmul, map_sum,
      LinearEquiv.coe_coe,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
      TensorProduct.map_tmul, comp_apply, mul'_apply]
    have hopf := mul_antipode_rTensor_comul_apply (R := R) (a * b)
    rw [Bialgebra.comul_mul, hsa, hsb] at hopf
    simp only [Finset.sum_mul, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
               map_sum, rTensor_tmul, mul'_apply] at hopf
    rw [hopf]
    congr 1
    rw [TensorProduct.counit_tmul, Bialgebra.counit_mul, Algebra.smul_def]
    simp [mul_comm]
  ext a b
  simp only [TensorProduct.AlgebraTensorModule.curry_apply]
  exact key a b

/-- Multiplicativity of the antipode in the commutative case: `S(ab) = S(a) S(b)`. (In the
commutative setting this matches the antihomomorphism law since `S(a) S(b) = S(b) S(a)`.) -/
theorem HopfAlgebra.antipode_mul_comm (a b : A) :
    antipode R (a * b) = antipode R a * antipode R b := by


  have h_left : (toConv HopfAlgebra.antimulComm : WithConv (A ⊗[R] A →ₗ[R] A)) *
      toConv (mul' R A) = 1 := HopfAlgebra.antimulComm_conv_mul
  have h_Smul_left : (toConv ((antipode R).comp (mul' R A)) : WithConv (A ⊗[R] A →ₗ[R] A)) *
      toConv (mul' R A) = 1 := HopfAlgebra.Smul_conv_mul
  have h_right : toConv (mul' R A) *
      (toConv HopfAlgebra.antimulComm : WithConv (A ⊗[R] A →ₗ[R] A)) = 1 :=
    HopfAlgebra.mul_conv_antimulComm
  have key : (toConv ((antipode R).comp (mul' R A)) : WithConv (A ⊗[R] A →ₗ[R] A)) =
      toConv HopfAlgebra.antimulComm :=
    calc toConv ((antipode R).comp (mul' R A))
        = toConv ((antipode R).comp (mul' R A)) * 1 := (mul_one _).symm
      _ = toConv ((antipode R).comp (mul' R A)) *
          (toConv (mul' R A) * toConv HopfAlgebra.antimulComm) := by rw [h_right]
      _ = (toConv ((antipode R).comp (mul' R A)) * toConv (mul' R A)) *
          toConv HopfAlgebra.antimulComm := (mul_assoc _ _ _).symm
      _ = 1 * toConv HopfAlgebra.antimulComm := by rw [h_Smul_left]
      _ = toConv HopfAlgebra.antimulComm := one_mul _
  have key' : (antipode R).comp (mul' R A) = HopfAlgebra.antimulComm :=
    toConv_injective key
  have := LinearMap.congr_fun key' (a ⊗ₜ[R] b)
  simp [HopfAlgebra.antimulComm_tmul, mul'_apply] at this
  exact this

end Proposition_1_22_1
