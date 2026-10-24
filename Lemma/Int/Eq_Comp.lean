import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w x

private lemma extend {K : Type u} [CommRing K] {A : Type v} [CommRing A] [Algebra K A] [Module.Finite K A] (C : Subalgebra K A) (Ω : Type x) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] (h : ↥C →ₐ[K] Ω) : ∃ ν : A →ₐ[K] Ω, ν.comp C.val = h := by
  classical
  let _ : Algebra.IsIntegral K A := inferInstance
  let _ : Algebra.IsIntegral ↥C A := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := K) x).tower_top⟩
  let 𝔭 : Ideal ↥C := RingHom.ker h.toRingHom
  let h𝔭 : 𝔭.IsPrime := RingHom.ker_isPrime h.toRingHom
  have hbot : ∀ c ∈ (⊥ : Ideal A).comap (algebraMap ↥C A), c ∈ 𝔭 := by
    intro c hc
    rw [Ideal.mem_comap, Ideal.mem_bot] at hc
    show h.toRingHom c = 0
    have : (c : A) = 0 := hc
    have hc0 : c = 0 := Subtype.ext this
    rw [hc0, map_zero]
  obtain ⟨Q, -, hQprime, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭 (⊥ : Ideal A) hbot
  let _ := hQprime
  let 𝔭' : Ideal ↥C := Q.comap (algebraMap ↥C A)
  have h𝔭' : 𝔭' = 𝔭 := hQ
  let _ : 𝔭'.IsPrime := by
    rw [h𝔭']
    apply h𝔭
  let _ : IsDomain (↥C ⧸ 𝔭') := Ideal.Quotient.isDomain 𝔭'
  let _ : IsDomain (A ⧸ Q) := Ideal.Quotient.isDomain Q
  have hker : ∀ c ∈ 𝔭', h.toRingHom c = 0 := by
    intro c hc
    rw [h𝔭'] at hc
    apply hc
  let h' : ↥C ⧸ 𝔭' →+* Ω := Ideal.Quotient.lift 𝔭' h.toRingHom hker
  let algΩ : Algebra (↥C ⧸ 𝔭') Ω := h'.toAlgebra
  have hkerle (c : ↥C) (hc : c ∈ RingHom.ker h.toRingHom) : c ∈ 𝔭' := by
    change h.toRingHom c = 0 at hc
    rw [h𝔭']
    apply hc
  have h'inj : Function.Injective h' := RingHom.lift_injective_of_ker_le_ideal 𝔭' hker hkerle
  let _ : Module.IsTorsionFree (↥C ⧸ 𝔭') Ω := by
    refine Module.IsTorsionFree.mk fun r hr => ?_
    intro a b hab
    refine mul_left_cancel₀ (a := algebraMap (↥C ⧸ 𝔭') Ω r) ?_ ?_
    ·
      intro h0
      apply hr.left.ne_zero
      apply h'inj
      change algebraMap (↥C ⧸ 𝔭') Ω r = h' 0
      rw [h0, map_zero]
    ·
      simpa [Algebra.smul_def] using hab
  let _ : FaithfulSMul (↥C ⧸ 𝔭') (A ⧸ Q) := (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.algebraMap_quotient_injective
  let _ : Module.IsTorsionFree (↥C ⧸ 𝔭') (A ⧸ Q) := by
    refine Module.IsTorsionFree.mk fun r hr => ?_
    intro a b hab
    refine mul_left_cancel₀ (a := algebraMap (↥C ⧸ 𝔭') (A ⧸ Q) r) ?_ ?_
    ·
      intro h0
      apply hr.left.ne_zero
      apply Ideal.algebraMap_quotient_injective
      rw [h0, map_zero]
    ·
      simpa [Algebra.smul_def] using hab
  let _ : Algebra.IsIntegral (↥C ⧸ 𝔭') (A ⧸ Q) := inferInstance
  let _ : Algebra.IsAlgebraic (↥C ⧸ 𝔭') (A ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let ψ : (A ⧸ Q) →ₐ[↥C ⧸ 𝔭'] Ω := IsAlgClosed.lift
  let ν₀ : A →+* Ω := ψ.toRingHom.comp (Ideal.Quotient.mk Q)
  have hν₀C : ∀ c : ↥C, ν₀ (c : A) = h c := by
    intro c
    show ψ (Ideal.Quotient.mk Q (algebraMap ↥C A c)) = h c
    have h1 : Ideal.Quotient.mk Q (algebraMap ↥C A c) = algebraMap (↥C ⧸ 𝔭') (A ⧸ Q) (Ideal.Quotient.mk 𝔭' c) := rfl
    rw [h1, AlgHom.commutes]
    show h' (Ideal.Quotient.mk 𝔭' c) = h c
    rw [Ideal.Quotient.lift_mk]
    rfl
  refine ⟨AlgHom.mk ν₀ ?_, ?_⟩
  ·
    intro k
    show ν₀ (algebraMap K A k) = algebraMap K Ω k
    have : algebraMap K A k = ((algebraMap K ↥C k : ↥C) : A) := rfl
    rw [this, hν₀C, AlgHom.commutes]
  ·
    apply AlgHom.ext
    intro c
    apply hν₀C c

/--
[Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subalgebra_exists_algHom_comp_val_eq_of_isAlgClosed_of_moduleFinite.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A] [Module.Finite R A]
  (C : Subalgebra R A) (Ω : Type w) [Field Ω] [Algebra R Ω] [IsAlgClosed Ω]
  (h : ↥C →ₐ[R] Ω) :
  -- imply
  ∃ ν : A →ₐ[R] Ω, ν.comp C.val = h :=
  extend C Ω h


-- created on 2026-10-20
