import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[RingHom_exists_algEquiv_comp_eq_of_ker_eq_of_forall_exists_mul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_exists_algEquiv_comp_eq_of_ker_eq_of_forall_exists_mul_eq.lean)
-/
@[path]
private lemma main
  {κ B K₁ K₂ C : Type} [Field κ] [CommRing B] [Field K₁] [Field K₂] [Algebra κ K₁] [Algebra κ K₂]
  (r₁ : RingHom B K₁)
  (r₂ : RingHom B K₂)
  (c : C → B)
  (cκ : C → κ)
  -- given
  (hker : RingHom.ker r₁ = RingHom.ker r₂)
  (hfrac₁ : ∀ x : K₁, ∃ g h : B, r₁ h ≠ 0 ∧ x * r₁ h = r₁ g)
  (hfrac₂ : ∀ x : K₂, ∃ g h : B, r₂ h ≠ 0 ∧ x * r₂ h = r₂ g)
  (hcκ : Function.Surjective cκ)
  (hc₁ : ∀ t : C, r₁ (c t) = algebraMap κ K₁ (cκ t))
  (hc₂ : ∀ t : C, r₂ (c t) = algebraMap κ K₂ (cκ t)) :
  -- imply
  ∃ e : AlgEquiv κ K₁ K₂, ∀ b : B, e (r₁ b) = r₂ b := by
  -- proof
  classical
  let D := B ⧸ RingHom.ker r₁
  let f₁ : RingHom D K₁ := RingHom.kerLift r₁
  let f₂ : RingHom D K₂ := Ideal.Quotient.lift (RingHom.ker r₁) r₂
    (fun a ha => by rwa [hker, RingHom.mem_ker] at ha)
  have hf₁ : Function.Injective f₁ := RingHom.kerLift_injective r₁
  have hf₂ : Function.Injective f₂ :=
    RingHom.lift_injective_of_ker_le_ideal _ _ (by rw [hker])
  let a₁ : Algebra D K₁ := f₁.toAlgebra
  let a₂ : Algebra D K₂ := f₂.toAlgebra
  have hA₁ : ∀ b : B, algebraMap D K₁ (Ideal.Quotient.mk _ b) = r₁ b := fun b => RingHom.kerLift_mk r₁ b
  have hA₂ : ∀ b : B, algebraMap D K₂ (Ideal.Quotient.mk _ b) = r₂ b := fun b => Ideal.Quotient.lift_mk _ _ _
  let _ : FaithfulSMul D K₁ := (faithfulSMul_iff_algebraMap_injective D K₁).mpr hf₁
  let _ : FaithfulSMul D K₂ := (faithfulSMul_iff_algebraMap_injective D K₂).mpr hf₂
  let _ : IsFractionRing D K₁ := IsFractionRing.of_field D K₁ (fun z => by
    obtain ⟨g, h, hh, e⟩ := hfrac₁ z
    refine ⟨Ideal.Quotient.mk _ g, Ideal.Quotient.mk _ h, ?_⟩
    rw [hA₁, hA₁, eq_div_iff hh, e])
  let _ : IsFractionRing D K₂ := IsFractionRing.of_field D K₂ (fun z => by
    obtain ⟨g, h, hh, e⟩ := hfrac₂ z
    refine ⟨Ideal.Quotient.mk _ g, Ideal.Quotient.mk _ h, ?_⟩
    rw [hA₂, hA₂, eq_div_iff hh, e])
  let e₀ : AlgEquiv D K₁ K₂ := IsLocalization.algEquiv (nonZeroDivisors D) K₁ K₂
  have he₀ : ∀ b : B, e₀ (r₁ b) = r₂ b := fun b => by
    rw [← hA₁, ← hA₂]
    apply e₀.commutes _
  refine ⟨AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (fun k => ?_), fun b => he₀ b⟩
  obtain ⟨t, rfl⟩ := hcκ k
  rw [← hc₁, ← hc₂]
  apply he₀ (c t)


-- created on 2026-10-20
