import Mathlib
import sympy.Basic
open scoped TensorProduct


noncomputable def antipodeAlgHom' (K : Type*) [CommRing K] (A : Type*) [CommRing A] [HopfAlgebra K A] :
  A →ₐ[K] A :=
  AlgHom.ofLinearMap (HopfAlgebraStruct.antipode (R := K))
    (HopfAlgebra.antipode_one (R := K) (A := A))
    (fun a b => by rw [HopfAlgebra.antipode_mul_antidistrib, mul_comm])

private lemma antipodeAlgHom'_apply {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
  (a : A) : antipodeAlgHom' K A a = HopfAlgebraStruct.antipode (R := K) a := rfl

private lemma exists_inv_point'
  {K : Type*} [CommRing K] {A : Type*} [CommRing A] [HopfAlgebra K A]
  {L : Type*} [CommRing L] [Algebra K L] (ν : A →ₐ[K] L) :
  ∃ ν' : A →ₐ[K] L, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := K) ∧
    WithConv.toConv ν' * WithConv.toConv ν = 1 ∧ WithConv.toConv ν * WithConv.toConv ν' = 1 := by
  refine ⟨ν.comp (antipodeAlgHom' K A), ?_, ?_, ?_⟩
  ·
    ext a; rfl
  ·
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    change (WithConv.toConv (ν.comp (antipodeAlgHom' K A)) * WithConv.toConv ν).ofConv a =
      (1 : WithConv (A →ₐ[K] L)).ofConv a
    rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
    have key : (Algebra.TensorProduct.lift (ν.comp (antipodeAlgHom' K A)) ν
      (fun _ _ => Commute.all _ _)).toLinearMap =
      ν.toLinearMap ∘ₗ LinearMap.mul' K A ∘ₗ (HopfAlgebraStruct.antipode (R := K)).rTensor A := by
      apply TensorProduct.ext'
      intro x y
      simp [Algebra.TensorProduct.lift_tmul, LinearMap.rTensor_tmul, antipodeAlgHom'_apply]
    have h := LinearMap.congr_fun key (Coalgebra.comul (R := K) a)
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at h
    change Algebra.TensorProduct.lift (ν.comp (antipodeAlgHom' K A)) ν _ (Coalgebra.comul (R := K) a) = _
    rw [h, HopfAlgebra.mul_antipode_rTensor_comul_apply, AlgHom.commutes]
  ·
    apply WithConv.ext
    apply AlgHom.ext
    intro a
    change (WithConv.toConv ν * WithConv.toConv (ν.comp (antipodeAlgHom' K A))).ofConv a =
      (1 : WithConv (A →ₐ[K] L)).ofConv a
    rw [AlgHom.convMul_apply, AlgHom.convOne_apply]
    have key : (Algebra.TensorProduct.lift ν (ν.comp (antipodeAlgHom' K A))
      (fun _ _ => Commute.all _ _)).toLinearMap =
      ν.toLinearMap ∘ₗ LinearMap.mul' K A ∘ₗ (HopfAlgebraStruct.antipode (R := K)).lTensor A := by
      apply TensorProduct.ext'
      intro x y
      simp [Algebra.TensorProduct.lift_tmul, LinearMap.lTensor_tmul, antipodeAlgHom'_apply]
    have h := LinearMap.congr_fun key (Coalgebra.comul (R := K) a)
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at h
    change Algebra.TensorProduct.lift ν (ν.comp (antipodeAlgHom' K A)) _ (Coalgebra.comul (R := K) a) = _
    rw [h, HopfAlgebra.mul_antipode_lTensor_comul_apply, AlgHom.commutes]
/--
[HopfAlgebra_exists_comp_antipode_convMul_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_exists_comp_antipode_convMul_eq_one.lean)
-/
@[path]
private lemma main
  [CommRing K] [CommRing A] [HopfAlgebra K A] [CommRing L] [Algebra K L]
  {ν : A →ₐ[K] L} :
-- imply
  ∃ ν' : A →ₐ[K] L, ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := K) ∧
      WithConv.toConv ν' * WithConv.toConv ν = 1 ∧ WithConv.toConv ν * WithConv.toConv ν' = 1 :=
  -- proof
  exists_inv_point' ν


-- created on 2026-10-23
