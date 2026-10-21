import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[RingHom_exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_exists_comp_eq_and_ker_eq_of_isIntegral_of_isAlgClosed.lean)
-/
@[path]
private lemma main
    {B₁ B Ω : Type*} [CommRing B₁] [CommRing B] [Field Ω] [IsAlgClosed Ω]
    (f : B₁ →+* B) (hf : f.IsIntegral)
    (φ₁ : B₁ →+* Ω) (y : Ideal B) [y.IsPrime]
    (hy : y.comap f = RingHom.ker φ₁) :
    ∃ φ : B →+* Ω, φ.comp f = φ₁ ∧ RingHom.ker φ = y := by
  let _ : Algebra B₁ B := f.toAlgebra
  let _ : Algebra.IsIntegral B₁ B := ⟨hf⟩
  set P : Ideal B₁ := y.comap (algebraMap B₁ B) with hPdef
  have hPy : P = RingHom.ker φ₁ := hy
  let _ : IsDomain (B ⧸ y) := Ideal.Quotient.isDomain y
  let _ : IsDomain (B₁ ⧸ P) := Ideal.Quotient.isDomain P
  let _ : Algebra.IsIntegral (B₁ ⧸ P) (B ⧸ y) := Algebra.IsIntegral.quotient
  let _ : Module.IsTorsionFree (B₁ ⧸ P) (B ⧸ y) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Ideal.algebraMap_quotient_injective
  have hP : ∀ a : B₁, a ∈ P → φ₁ a = 0 := fun a ha => by
    rw [hPy] at ha
    exact RingHom.mem_ker.mp ha
  let ψ : B₁ ⧸ P →+* Ω := Ideal.Quotient.lift P φ₁ hP
  have hψinj : Function.Injective ψ := by
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_quotient_lift, ← hPy]
    exact Ideal.map_quotient_self P
  let _ : Algebra (B₁ ⧸ P) Ω := ψ.toAlgebra
  let _ : Module.IsTorsionFree (B₁ ⧸ P) Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hψinj
  let Φ : (B ⧸ y) →ₐ[B₁ ⧸ P] Ω := IsAlgClosed.lift
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hker : RingHom.ker (Φ : (B ⧸ y) →+* Ω) = ⊥ := by
      refine Ideal.eq_bot_of_comap_eq_bot (R := B₁ ⧸ P) ?_
      ext r
      rw [Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
      show Φ (algebraMap (B₁ ⧸ P) (B ⧸ y) r) = 0 ↔ r = 0
      rw [Φ.commutes, RingHom.algebraMap_toAlgebra, map_eq_zero_iff ψ hψinj]
    have : x ∈ RingHom.ker (Φ : (B ⧸ y) →+* Ω) := (RingHom.mem_ker).mpr hx
    rw [hker] at this
    exact (Submodule.mem_bot _).mp this
  refine ⟨(Φ : (B ⧸ y) →+* Ω).comp (Ideal.Quotient.mk y), ?_, ?_⟩
  · ext b
    show Φ (Ideal.Quotient.mk y (f b)) = φ₁ b
    have : Ideal.Quotient.mk y (f b) = algebraMap (B₁ ⧸ P) (B ⧸ y) (Ideal.Quotient.mk P b) := rfl
    rw [this, Φ.commutes]
    show ψ (Ideal.Quotient.mk P b) = φ₁ b
    exact Ideal.Quotient.lift_mk P φ₁ hP
  · ext b
    rw [RingHom.mem_ker, RingHom.comp_apply]
    show Φ (Ideal.Quotient.mk y b) = 0 ↔ b ∈ y
    rw [map_eq_zero_iff _ hΦinj, Ideal.Quotient.eq_zero_iff_mem]

-- created on 2026-10-20
