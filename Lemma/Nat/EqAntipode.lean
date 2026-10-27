import Mathlib
import Initialize.Tactic.Attr.Basic
open Coalgebra HopfAlgebra
open scoped TensorProduct Coalgebra.TensorProduct


private lemma antipode_algebraMap'
  {R : Type*}
  [CommSemiring R]
  {A : Type*}
  [Semiring A]
  [HopfAlgebra R A]
  (r : R) :
  antipode R (algebraMap R A r) = algebraMap R A r := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, antipode_one]

private lemma toConv_antipode_mul_toConv_id'
  {R : Type*}
  [CommSemiring R]
  {A : Type*}
  [Semiring A]
  [HopfAlgebra R A] :
  WithConv.toConv (antipode R (A := A)) * WithConv.toConv (LinearMap.id : A →ₗ[R] A)
    = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.id_coe, id_eq]
  exact sum_antipode_mul_eq_algebraMap_counit (ℛ R a)

private lemma sum_antipode_antipode_mul_antipode'
  {R : Type*}
  [CommSemiring R]
  {A : Type*}
  [CommSemiring A]
  [HopfAlgebra R A]
  {a : A} {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R a ι𝓡) :
  ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i)) * antipode R (𝓡.right i)
    = algebraMap R A (counit (R := R) a) := calc
    _ = ∑ i ∈ 𝓡.index, antipode R (antipode R (𝓡.left i) * 𝓡.right i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [antipode_mul_antidistrib (antipode R (𝓡.left i)) (𝓡.right i)]
      exact mul_comm _ _
    _ = antipode R (∑ i ∈ 𝓡.index, antipode R (𝓡.left i) * 𝓡.right i) := by
      rw [map_sum]
    _ = antipode R (algebraMap R A (counit (R := R) a)) := by
      rw [sum_antipode_mul_eq_algebraMap_counit 𝓡]
    _ = algebraMap R A (counit (R := R) a) := antipode_algebraMap' _

private lemma toConv_antipode_comp_antipode_mul_toConv_antipode'
  {R : Type*}
  [CommSemiring R]
  {A : Type*}
  [CommSemiring A]
  [HopfAlgebra R A] :
  WithConv.toConv (antipode R ∘ₗ antipode R : A →ₗ[R] A)
    * WithConv.toConv (antipode R (A := A))
    = (1 : WithConv (A →ₗ[R] A)) := by
  refine WithConv.ext (LinearMap.ext fun a => ?_)
  simp only [LinearMap.convMul_def, LinearMap.convOne_def, WithConv.ofConv_toConv,
    LinearMap.comp_apply, Algebra.linearMap_apply]
  rw [← (ℛ R a).eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, LinearMap.comp_apply]
  exact sum_antipode_antipode_mul_antipode' (ℛ R a)

private lemma antipode_comp_antipode'
  {R : Type*}
  [CommSemiring R]
  {A : Type*}
  [CommSemiring A]
  [HopfAlgebra R A] :
  (antipode R ∘ₗ antipode R : A →ₗ[R] A) = LinearMap.id :=
  WithConv.toConv_injective
    (left_inv_eq_right_inv toConv_antipode_comp_antipode_mul_toConv_antipode'
      toConv_antipode_mul_toConv_id')
/--
[HopfAlgebra_antipode_antipode](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_antipode_antipode.lean)
-/
@[path]
private lemma main
  [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
  {a : A} :
-- imply
  HopfAlgebra.antipode R (HopfAlgebra.antipode R a) = a := by
-- proof
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (antipode_comp_antipode' (R := R) (A := A)) a


-- created on 2026-10-23
