import Mathlib
import sympy.Basic
open Module
open scoped TensorProduct


private lemma lid_rTensor_sum
  [CommRing R] [CommRing A] [Algebra R A]
  (φ : Dual R A) (S : Finset (A × A)) :
  TensorProduct.lid R A (LinearMap.rTensor A φ (∑ p ∈ S, p.1 ⊗ₜ[R] p.2)) = ∑ p ∈ S, φ p.1 • p.2 := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

private lemma trace_main
  [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A]
  (τ : Dual R A) (Δ : A ⊗[R] A)
-- given
  (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
  (hτ : TensorProduct.lid R A (LinearMap.rTensor A τ Δ) = 1)
  (x : A) :
-- imply
  Algebra.trace R A x = τ (LinearMap.mul' R A Δ * x) := by
-- proof
  classical
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset Δ
  have hone : ∑ p ∈ S, τ p.1 • p.2 = 1 := by
    rw [← lid_rTensor_sum τ S, ← hS, hτ]
  have key : ∀ a : A, ∑ p ∈ S, τ (a * p.1) • p.2 = a := by
    intro a
    have hl : (a ⊗ₜ[R] (1 : A)) * Δ = ∑ p ∈ S, (a * p.1) ⊗ₜ[R] p.2 := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hr : ((1 : A) ⊗ₜ[R] a) * Δ = ∑ p ∈ S, p.1 ⊗ₜ[R] (a * p.2) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h := congrArg (fun z => TensorProduct.lid R A (LinearMap.rTensor A τ z)) (hbal a)
    simp only [hl, hr, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h
    rw [h]
    calc
      _ = a * ∑ p ∈ S, τ p.1 • p.2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [mul_smul_comm]
      _ = a := by rw [hone, mul_one]
  have hlmul : Algebra.lmul R A x =
      dualTensorHom R A A (∑ p ∈ S, (τ.comp (LinearMap.mulLeft R (x * p.1))) ⊗ₜ[R] p.2) := by
    apply LinearMap.ext
    intro m
    rw [map_sum, LinearMap.sum_apply]
    simp only [dualTensorHom_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    have := key (x * m)
    calc
      _ = x * m := rfl
      _ = ∑ p ∈ S, τ (x * m * p.1) • p.2 := this.symm
      _ = ∑ p ∈ S, τ (x * p.1 * m) • p.2 := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [mul_right_comm]
  rw [Algebra.trace_apply, hlmul, LinearMap.trace_eq_contract_apply, map_sum]
  simp only [contractLeft_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [← map_sum]
  congr 1
  rw [hS, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [LinearMap.mul'_apply]
  ring


/--
[Algebra_trace_eq_dual_lmul_of_bijective_rTensor](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_trace_eq_dual_lmul_of_bijective_rTensor.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A]
  {τ : Dual R A} {Δ : A ⊗[R] A}
-- given
  (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
  (_ : Function.Bijective (fun φ : Dual R A => TensorProduct.lid R A (LinearMap.rTensor A φ Δ)))
  (hτ : TensorProduct.lid R A (LinearMap.rTensor A τ Δ) = 1)
  {x : A} :
-- imply
  Algebra.trace R A x = τ (LinearMap.mul' R A Δ * x) := by
-- proof
  apply trace_main τ Δ hbal hτ x


-- created on 2026-10-13
