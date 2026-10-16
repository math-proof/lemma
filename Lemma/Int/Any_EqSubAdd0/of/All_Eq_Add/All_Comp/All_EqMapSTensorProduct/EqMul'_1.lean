import Mathlib
import sympy.Basic
open scoped TensorProduct


private noncomputable def extK
  {k : Type u} {Λ : Type v} {P : Type w} [CommRing k] [Ring Λ] [AddCommGroup P] [Module k P]
  (φ : Λ →ₗ[ℤ] P) : k ⊗[ℤ] Λ →ₗ[k] P :=
  TensorProduct.AlgebraTensorModule.lift ((LinearMap.id : k →ₗ[k] k).smulRight φ)

private lemma extK_tmul
  {k : Type u} {Λ : Type v} {P : Type w} [CommRing k] [Ring Λ] [AddCommGroup P] [Module k P]
  {φ : Λ →ₗ[ℤ] P} {c : k} {x : Λ} :
-- imply
  extK φ (c ⊗ₜ[ℤ] x) = c • φ x := by
-- proof
  rw [extK, TensorProduct.AlgebraTensorModule.lift_tmul]
  rfl


/--
[Algebra_exists_forall_add_sub_eq_zero_of_map_mul_of_separabilityElement_tensor](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_forall_add_sub_eq_zero_of_map_mul_of_separabilityElement_tensor.lean)
-/
@[path]
private lemma main
  {k : Type u} {Λ : Type v} [CommRing k] [Ring Λ]
  {M : Type w} [AddCommGroup M] [Module k M]
  {e : (k ⊗[ℤ] Λ) ⊗[k] (k ⊗[ℤ] Λ)}
  {θ : Λ →+* Module.End k M} {ρ : Λᵐᵒᵖ →+* Module.End k M}
  {o : Λ →+ M}
-- given
  (he₁ : LinearMap.mul' k (k ⊗[ℤ] Λ) e = 1)
  (he₂ : ∀ x : k ⊗[ℤ] Λ, _root_.TensorProduct.map (LinearMap.mulLeft k x) LinearMap.id e =
    _root_.TensorProduct.map LinearMap.id (LinearMap.mulRight k x) e)
  (hθρ : ∀ (x : Λ) (y : Λᵐᵒᵖ), (θ x).comp (ρ y) = (ρ y).comp (θ x))
  (ho : ∀ x y : Λ, o (x * y) = θ x (o y) + ρ (MulOpposite.op y) (o x)) :
-- imply
  ∃ ξ : M, ∀ x : Λ, o x + θ x ξ - ρ (MulOpposite.op x) ξ = 0 := by
-- proof
  classical
  let δ : k ⊗[ℤ] Λ →ₗ[k] M := extK o.toIntLinearMap
  let Θ : k ⊗[ℤ] Λ →ₗ[k] Module.End k M := extK θ.toAddMonoidHom.toIntLinearMap
  let Ρ : k ⊗[ℤ] Λ →ₗ[k] Module.End k M :=
    extK ((ρ.toAddMonoidHom.comp (MulOpposite.opAddEquiv : Λ ≃+ Λᵐᵒᵖ).toAddMonoidHom).toIntLinearMap)
  have hδ : ∀ (c : k) (x : Λ), δ (c ⊗ₜ[ℤ] x) = c • o x := fun c x => by
    rw [extK_tmul]
    rfl
  have hΘ : ∀ (c : k) (x : Λ), Θ (c ⊗ₜ[ℤ] x) = c • θ x := fun c x => by
    rw [extK_tmul]
    rfl
  have hΡ : ∀ (c : k) (x : Λ), Ρ (c ⊗ₜ[ℤ] x) = c • ρ (MulOpposite.op x) := fun c x => by
    rw [extK_tmul]
    rfl
  have hΡmul : ∀ a b : k ⊗[ℤ] Λ, Ρ (a * b) = Ρ b * Ρ a := by
    intro a b
    induction a using TensorProduct.inductionOn with
    | tmul c x =>
      induction b using TensorProduct.inductionOn with
      | tmul c' y =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hΡ, hΡ, hΡ, MulOpposite.op_mul, map_mul,
          smul_mul_smul_comm, mul_comm c' c]
      | add b₁ b₂ h₁ h₂ => simp [mul_add, map_add, h₁, h₂, add_mul]
    | add a₁ a₂ h₁ h₂ => simp [add_mul, map_add, h₁, h₂, mul_add]
  have hΡone : Ρ 1 = 1 := by
    rw [Algebra.TensorProduct.one_def, hΡ, one_smul, MulOpposite.op_one, map_one]
  have hcomm : ∀ a b : k ⊗[ℤ] Λ, Θ a * Ρ b = Ρ b * Θ a := by
    intro a b
    induction a using TensorProduct.inductionOn with
    | tmul c x =>
      induction b using TensorProduct.inductionOn with
      | tmul c' y =>
        rw [hΘ, hΡ, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm c c']
        congr 1
        apply hθρ x (MulOpposite.op y)
      | add b₁ b₂ h₁ h₂ => simp [map_add, add_mul, mul_add, h₁, h₂]
    | add a₁ a₂ h₁ h₂ => simp [map_add, add_mul, mul_add, h₁, h₂]
  have hcoc : ∀ a b : k ⊗[ℤ] Λ, δ (a * b) = Θ a (δ b) + Ρ b (δ a) := by
    intro a b
    induction a using TensorProduct.inductionOn with
    | tmul c x =>
      induction b using TensorProduct.inductionOn with
      | tmul c' y =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hδ, hδ, hδ, hΘ, hΡ, ho, smul_add,
          LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul, smul_smul, smul_smul,
          mul_comm c' c]
      | add b₁ b₂ h₁ h₂ =>
        simp [mul_add, map_add, h₁, h₂, LinearMap.add_apply]
        abel
    | add a₁ a₂ h₁ h₂ =>
      simp [add_mul, map_add, h₁, h₂, LinearMap.add_apply]
      abel
  let B : (k ⊗[ℤ] Λ) →ₗ[k] (k ⊗[ℤ] Λ) →ₗ[k] M := LinearMap.mk₂ k (fun u v => Ρ v (δ u))
    (fun u₁ u₂ v => by rw [map_add, map_add])
    (fun c u v => by rw [map_smul, map_smul])
    (fun u v₁ v₂ => by rw [map_add, LinearMap.add_apply])
    (fun c u v => by rw [map_smul, LinearMap.smul_apply])
  let Φ : (k ⊗[ℤ] Λ) ⊗[k] (k ⊗[ℤ] Λ) →ₗ[k] M := TensorProduct.lift B
  have hΦ : ∀ u v, Φ (u ⊗ₜ[k] v) = Ρ v (δ u) := fun u v => TensorProduct.lift.tmul u v
  obtain ⟨T, hT⟩ := TensorProduct.exists_finset e
  set m' : M := ∑ p ∈ T, Ρ p.2 (δ p.1) with hm'
  have hsum1 : ∑ p ∈ T, p.1 * p.2 = 1 := by
    have h := he₁
    rw [hT, map_sum] at h
    simpa [LinearMap.mul'_apply] using h
  have key : ∀ a : k ⊗[ℤ] Λ, Θ a m' + δ a = Ρ a m' := by
    intro a
    have hL : Φ (_root_.TensorProduct.map (LinearMap.mulLeft k a) LinearMap.id e) = Θ a m' + δ a := by
      rw [hT, map_sum, map_sum]
      simp [TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_apply, hΦ, hcoc, map_add]
      rw [Finset.sum_add_distrib]
      congr 1
      ·
        rw [hm', map_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Module.End.mul_apply, ← hcomm, Module.End.mul_apply]
      ·
        have h1 : ∀ p ∈ T, Ρ p.2 (Ρ p.1 (δ a)) = Ρ (p.1 * p.2) (δ a) := by
          intro p _
          rw [hΡmul, Module.End.mul_apply]
        rw [Finset.sum_congr rfl h1, ← LinearMap.sum_apply, ← map_sum, hsum1, hΡone,
          Module.End.one_apply]
    have hR : Φ (_root_.TensorProduct.map LinearMap.id (LinearMap.mulRight k a) e) = Ρ a m' := by
      rw [hT, map_sum, map_sum]
      simp [TensorProduct.map_tmul, LinearMap.mulRight_apply, LinearMap.id_apply, hΦ]
      rw [hm', map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [hΡmul, Module.End.mul_apply]
    rw [← hL, ← hR, he₂ a]
  refine ⟨m', fun x => ?_⟩
  have hx := key ((1 : k) ⊗ₜ[ℤ] x)
  rw [hΘ, hδ, hΡ, one_smul, one_smul, one_smul] at hx
  rw [← hx]
  abel


-- created on 2026-10-13
