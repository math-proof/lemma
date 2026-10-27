import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_of_isUnit_of_charZero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_isDedekindDomain_ringHom_flat_of_isUnit_of_charZero.lean)
-/
@[path]
private lemma main
  (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪]
  (n : ℕ)
  (hn : IsUnit ((n : ℕ) : 𝒪)) :
  ∃ (B₀ : Type) (_ : CommRing B₀) (_ : IsDedekindDomain B₀) (i : RingHom B₀ 𝒪), Flat (Spec.map (CommRingCat.ofHom i)) ∧ IsUnit ((n : ℕ) : B₀) := by
  classical
  have hn0' : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast hn0'
  let B₀ := Localization.Away (n : ℤ)
  have hM : Submonoid.powers (n : ℤ) ≤ nonZeroDivisors ℤ := powers_le_nonZeroDivisors_of_noZeroDivisors hn0
  let _ : IsDomain B₀ := IsLocalization.isDomain_localization hM
  let _ : IsDedekindDomain B₀ := IsLocalization.isDedekindDomain ℤ hM B₀
  have hnO : IsUnit (Int.castRingHom 𝒪 (n : ℤ)) := by simpa using hn
  let i : RingHom B₀ 𝒪 := Localization.awayLift (Int.castRingHom 𝒪) (n : ℤ) hnO
  have hi_alg : ∀ z : ℤ, i (algebraMap ℤ B₀ z) = (z : 𝒪) := fun z => by
    simp [i, IsLocalization.Away.lift]
  have hinj : Function.Injective i := by
    intro x y hxy
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (n : ℤ)) x
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (n : ℤ)) y
    rw [IsLocalization.mk'_eq_iff_eq]
    have ha := congrArg (fun w => w * i (algebraMap ℤ B₀ s) * i (algebraMap ℤ B₀ t)) hxy
    simp only at ha
    have e1 : i (IsLocalization.mk' B₀ a s) * i (algebraMap ℤ B₀ ↑s) = i (algebraMap ℤ B₀ a) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    have e2 : i (IsLocalization.mk' B₀ b t) * i (algebraMap ℤ B₀ ↑t) = i (algebraMap ℤ B₀ b) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    have : i (algebraMap ℤ B₀ a) * i (algebraMap ℤ B₀ ↑t) = i (algebraMap ℤ B₀ b) * i (algebraMap ℤ B₀ ↑s) := calc
      _ = i (IsLocalization.mk' B₀ a s) * i (algebraMap ℤ B₀ ↑s) * i (algebraMap ℤ B₀ ↑t) := by rw [e1]
      _ = i (IsLocalization.mk' B₀ b t) * i (algebraMap ℤ B₀ ↑t) * i (algebraMap ℤ B₀ ↑s) := by
        rw [ha]
        ring
      _ = i (algebraMap ℤ B₀ b) * i (algebraMap ℤ B₀ ↑s) := by rw [e2]
    rw [hi_alg, hi_alg, hi_alg, hi_alg] at this
    have : ((a * (t : ℤ) : ℤ) : 𝒪) = ((b * (s : ℤ) : ℤ) : 𝒪) := by
      push_cast
      apply this
    have hab := Int.cast_injective this
    congr 1
    linear_combination hab
  let _ : Algebra B₀ 𝒪 := i.toAlgebra
  have hflat : Module.Flat B₀ 𝒪 := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨⟨a, ha⟩, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    change (a : B₀) • x = 0 at hax
    rw [Algebra.smul_def, mul_eq_zero] at hax
    obtain h | h := hax
    ·
      exfalso
      have : (a : B₀) = 0 := hinj (by simpa [map_zero, RingHom.algebraMap_toAlgebra i] using h)
      apply nonZeroDivisors.ne_zero ha this
    · apply h
  refine ⟨B₀, inferInstance, inferInstance, i, ?_, ?_⟩
  ·
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    apply hflat
  ·
    have : ((n : ℕ) : B₀) = algebraMap ℤ B₀ (n : ℤ) := by simp
    rw [this]
    apply IsLocalization.Away.algebraMap_isUnit (n : ℤ)


-- created on 2026-10-20
