import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[AlgHom_exists_rangeRestrict_factor_of_ker_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_exists_rangeRestrict_factor_of_ker_eq.lean)
-/
@[path]
private lemma main
  [CommRing A] [CommRing B] [Algebra A B] [CommRing K] [Algebra A K]
  {φ₁ φ₂ : B →ₐ[A] K}
-- given
  (h : RingHom.ker φ₁.toRingHom = RingHom.ker φ₂.toRingHom) :
-- imply
  ∃ (ψ : B →ₐ[A] ↥φ₁.range) (κ₂ : ↥φ₁.range →ₐ[A] K),
      Function.Surjective ψ ∧ Function.Injective κ₂ ∧
      (∀ b : B, ((ψ b : ↥φ₁.range) : K) = φ₁ b) ∧ (∀ b : B, κ₂ (ψ b) = φ₂ b) := by
-- proof
  classical
  have hsurj : Function.Surjective φ₁.rangeRestrict := φ₁.rangeRestrict_surjective
  have hker : ∀ b : B, b ∈ RingHom.ker φ₁.rangeRestrict.toRingHom ↔ φ₂ b = 0 := by
    intro b
    have h2 : b ∈ RingHom.ker φ₂.toRingHom ↔ φ₂ b = 0 := RingHom.mem_ker
    rw [← h2, ← h, RingHom.mem_ker, RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    rw [← Subtype.coe_inj]
    simp
  let I := RingHom.ker φ₁.rangeRestrict.toRingHom
  let e : (B ⧸ I) ≃ₐ[A] ↥φ₁.range := Ideal.quotientKerAlgEquivOfSurjective hsurj
  let lam : (B ⧸ I) →ₐ[A] K := Ideal.Quotient.liftₐ I φ₂ (fun b hb => (hker b).mp hb)
  refine ⟨φ₁.rangeRestrict, lam.comp (e.symm : ↥φ₁.range →ₐ[A] (B ⧸ I)), hsurj, ?_, fun b => rfl, ?_⟩
  ·
    rw [AlgHom.coe_comp]
    apply Function.Injective.comp _ e.symm.injective
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have : φ₂ b = 0 := by
      have hcomp := Ideal.Quotient.liftₐ_comp (R₁ := A) I φ₂ (fun a ha => (hker a).mp ha)
      have hb : φ₂ b = lam (Ideal.Quotient.mkₐ A I b) := by
        rw [← hcomp]
        rfl
      rw [hb, Ideal.Quotient.mkₐ_eq_mk, hz]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact (hker b).mpr this
  ·
    intro b
    have he : e (Ideal.Quotient.mk I b) = φ₁.rangeRestrict b := by
      show Ideal.kerLiftAlg φ₁.rangeRestrict (Ideal.Quotient.mk _ b) = _
      exact Ideal.kerLiftAlg_mk _ _
    show lam (e.symm (φ₁.rangeRestrict b)) = φ₂ b
    rw [← he, AlgEquiv.symm_apply_apply]
    have hcomp := Ideal.Quotient.liftₐ_comp (R₁ := A) I φ₂ (fun a ha => (hker a).mp ha)
    have : φ₂ b = lam (Ideal.Quotient.mkₐ A I b) := by
      rw [← hcomp]
      rfl
    rw [this, Ideal.Quotient.mkₐ_eq_mk]


-- created on 2026-10-10
