import Mathlib
import sympy.Basic
open scoped TensorProduct


private lemma exists_mul_one_tmul_eq
  {R : Type} [CommRing R] [IsDomain R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type} [CommRing H] [Algebra R H]
  {e : H} {γ : K ⊗[R] H}
-- given
  (hdiv : ∀ d : R, d ≠ 0 → ∀ y : H, ∃ z : H, d • (z * (1 - e)) = y * (1 - e)) :
-- imply
  ∃ m : H, γ * ((1 : K) ⊗ₜ[R] (1 - e)) = (1 : K) ⊗ₜ[R] (m * (1 - e)) := by
-- proof
  induction γ using TensorProduct.inductionOn with
  | tmul k y =>
    obtain ⟨r, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) k
    have hd0 : (d : R) ≠ 0 := nonZeroDivisors.ne_zero hd
    have hdK : algebraMap R K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    obtain ⟨z, hz⟩ := hdiv d hd0 (r • y)
    refine ⟨z, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have hk : algebraMap R K r / algebraMap R K d = r • (algebraMap R K d)⁻¹ := by
      rw [div_eq_inv_mul, Algebra.smul_def, mul_comm]
    rw [hk, TensorProduct.smul_tmul, ← smul_mul_assoc, ← hz, ← TensorProduct.smul_tmul, Algebra.smul_def,
      mul_inv_cancel₀ hdK]
  | add x y hx hy =>
    obtain ⟨m₁, h₁⟩ := hx
    obtain ⟨m₂, h₂⟩ := hy
    refine ⟨m₁ + m₂, ?_⟩
    rw [add_mul, h₁, h₂, add_mul, TensorProduct.tmul_add]


private lemma exists_section
  {R : Type} [CommRing R] [IsDomain R]
  {H : Type} [CommRing H] [Algebra R H]
  {S : Type} [CommRing S] [Algebra R S]
  {e : H} {πf : H →ₐ[R] S}
-- given
  (he : IsIdempotentElem e)
  (hπf : Function.Surjective πf)
  (hkerf : RingHom.ker πf = Ideal.span {1 - e}) :
-- imply
  ∃ σ : S →ₗ[R] H, ∀ h : H, σ (πf h) = h * e := by
-- proof
  let μ : H →ₗ[R] H := LinearMap.mulRight R e
  have hμ : LinearMap.ker πf.toLinearMap ≤ LinearMap.ker μ := by
    intro h hh
    rw [LinearMap.mem_ker] at hh ⊢
    change h * e = 0
    have hh' : h ∈ RingHom.ker πf := hh
    rw [hkerf, Ideal.mem_span_singleton] at hh'
    obtain ⟨x, rfl⟩ := hh'
    rw [mul_assoc, mul_comm x e, ← mul_assoc, sub_mul, one_mul, he.eq, sub_self, zero_mul]
  let μ' := (LinearMap.ker πf.toLinearMap).liftQ μ hμ
  let ε := πf.toLinearMap.quotKerEquivOfSurjective hπf
  refine ⟨μ'.comp ε.symm.toLinearMap, fun h => ?_⟩
  rw [LinearMap.comp_apply]
  show μ' ((πf.toLinearMap.quotKerEquivOfSurjective hπf).symm (πf.toLinearMap h)) = h * e
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply (f := πf.toLinearMap) hπf]
  rw [Submodule.liftQ_apply]
  rfl


private lemma baseChange_section_map
  {R : Type} [CommRing R]
  {K : Type} [Field K] [Algebra R K]
  {H : Type} [CommRing H] [Algebra R H]
  {S : Type} [CommRing S] [Algebra R S]
  {e : H} {πf : H →ₐ[R] S} {σ : S →ₗ[R] H} {γ : K ⊗[R] H}
-- given
  (hσ : ∀ h : H, σ (πf h) = h * e) :
-- imply
  σ.baseChange K (Algebra.TensorProduct.map (AlgHom.id K K) πf γ) = γ * ((1 : K) ⊗ₜ[R] e) := by
-- proof
  induction γ using TensorProduct.inductionOn with
  | tmul k h =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, LinearMap.baseChange_tmul, hσ,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, add_mul]


private lemma exists_eq_one_tmul
  {R : Type} [CommRing R] [IsDomain R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type} [CommRing H] [Algebra R H]
  {S : Type} [CommRing S] [Algebra R S]
  {e : H} {πf : H →ₐ[R] S} {β : K ⊗[R] H} {a : S}
-- given
  (he : IsIdempotentElem e)
  (hdiv : ∀ d : R, d ≠ 0 → ∀ y : H, ∃ z : H, d • (z * (1 - e)) = y * (1 - e))
  (hπf : Function.Surjective πf)
  (hkerf : RingHom.ker πf = Ideal.span {1 - e})
  (hβa : Algebra.TensorProduct.map (AlgHom.id K K) πf β = (1 : K) ⊗ₜ[R] a) :
-- imply
  ∃ h : H, β = (1 : K) ⊗ₜ[R] h ∧ πf h = a := by
-- proof
  obtain ⟨σ, hσ⟩ := exists_section he hπf hkerf
  obtain ⟨h₀, rfl⟩ := hπf a
  obtain ⟨m, hm⟩ := exists_mul_one_tmul_eq (γ := β) hdiv
  have he_part : β * ((1 : K) ⊗ₜ[R] e) = (1 : K) ⊗ₜ[R] (h₀ * e) := by
    rw [← baseChange_section_map (σ := σ) hσ, hβa, LinearMap.baseChange_tmul, hσ]
  have hπe : πf (1 - e) = 0 := by
    rw [← RingHom.mem_ker, hkerf]
    apply Ideal.mem_span_singleton_self
  have hπe' : πf e = 1 := by
    have := hπe
    rw [map_sub, map_one, sub_eq_zero] at this
    apply this.symm
  refine ⟨h₀ * e + m * (1 - e), ?_, ?_⟩
  ·
    calc
      _ = β * ((1 : K) ⊗ₜ[R] e) + β * ((1 : K) ⊗ₜ[R] (1 - e)) := by
        rw [← mul_add, ← TensorProduct.tmul_add, add_sub_cancel, ← Algebra.TensorProduct.one_def, mul_one]
      _ = (1 : K) ⊗ₜ[R] (h₀ * e + m * (1 - e)) := by
        rw [he_part, hm, TensorProduct.tmul_add]
  · rw [map_add, map_mul, map_mul, hπe, mul_zero, add_zero, hπe', mul_one]


/--
[Algebra_TensorProduct_exists_eq_one_tmul_of_map_eq_one_tmul_of_mul_one_tmul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_exists_eq_one_tmul_of_map_eq_one_tmul_of_mul_one_tmul_eq.lean)
-/
@[path]
private lemma main
  {R : Type} [CommRing R] [IsDomain R]
  {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {H : Type} [CommRing H] [Algebra R H]
  {S : Type} [CommRing S] [Algebra R S]
  {e f : H} {πf : H →ₐ[R] S} {β : K ⊗[R] H} {a : S}
-- given
  (he : IsIdempotentElem e)
  (_ : IsIdempotentElem f)
  (_ : f * e = e)
  (hdiv : ∀ d : R, d ≠ 0 → ∀ y : H, ∃ z : H, d • (z * (1 - e)) = y * (1 - e))
  (hπf : Function.Surjective πf)
  (hkerf : RingHom.ker πf = Ideal.span {1 - e})
  (_ : β * ((1 : K) ⊗ₜ[R] f) = β)
  (hβa : Algebra.TensorProduct.map (AlgHom.id K K) πf β = (1 : K) ⊗ₜ[R] a) :
-- imply
  ∃ h : H, β = (1 : K) ⊗ₜ[R] h ∧ πf h = a :=
-- proof
  exists_eq_one_tmul he hdiv hπf hkerf hβa


-- created on 2026-10-16
