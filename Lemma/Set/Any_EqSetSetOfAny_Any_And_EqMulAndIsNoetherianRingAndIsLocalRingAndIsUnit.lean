import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_subalgebra_coe_eq_isNoetherianRing_isLocalRing_isUnit_iff.lean)
-/
@[path]
private lemma main
  {A₀ : Type u} [CommRing A₀]
  {R : Type u} [CommRing R] [IsLocalRing R] [Algebra A₀ R]
  (T : Subalgebra A₀ R) [IsNoetherianRing ↥T] :
  -- imply
  ∃ S : Subalgebra A₀ R, (S : Set R) = {x : R | ∃ t ∈ T, ∃ u ∈ T, u ∉ IsLocalRing.maximalIdeal R ∧ x * u = t} ∧ IsNoetherianRing ↥S ∧ IsLocalRing ↥S ∧ ∀ x : ↥S, IsUnit x ↔ IsUnit (x : R) := by
  -- proof
  classical
  let 𝔭 : Ideal ↥T := (IsLocalRing.maximalIdeal R).comap T.val.toRingHom
  let h𝔭 : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  have hunitR : ∀ u : ↥T, u ∉ 𝔭 ↔ IsUnit (u : R) := by
    intro u
    change (u : R) ∉ IsLocalRing.maximalIdeal R ↔ IsUnit (u : R)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  have hM : ∀ y : 𝔭.primeCompl, IsUnit (T.val.toRingHom (y : ↥T)) := fun y => (hunitR y.1).mp (Ideal.mem_primeCompl_iff.mp y.2)
  let ψ : Localization.AtPrime 𝔭 →+* R := IsLocalization.lift (M := 𝔭.primeCompl) hM
  have hψT : ∀ t : ↥T, ψ (algebraMap ↥T _ t) = (t : R) := fun t => IsLocalization.lift_eq hM t
  have hψmk : ∀ (t : ↥T) (u : 𝔭.primeCompl), ψ (IsLocalization.mk' _ t u) * (u : R) = (t : R) := by
    intro t u
    have := IsLocalization.lift_mk'_spec (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) hM t u
    rw [← hψT t, ← IsLocalization.mk'_spec (Localization.AtPrime 𝔭) t u, map_mul, hψT]
  have hcomm : ∀ a : A₀, ψ (algebraMap A₀ (Localization.AtPrime 𝔭) a) = algebraMap A₀ R a := by
    intro a
    rw [IsScalarTower.algebraMap_apply A₀ ↥T (Localization.AtPrime 𝔭), hψT]
    rfl
  let ψₐ : Localization.AtPrime 𝔭 →ₐ[A₀] R := { toRingHom := ψ, commutes' := hcomm }
  have hψinj : Function.Injective ψₐ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl x
    change ψ (IsLocalization.mk' _ t u) = 0 at hx
    have h := hψmk t u
    rw [hx, zero_mul] at h
    have ht : t = 0 := by
      apply Subtype.ext
      rw [← h]
      rfl
    change IsLocalization.mk' (Localization.AtPrime 𝔭) t u = 0
    rw [ht, IsLocalization.mk'_zero]
  let e : Localization.AtPrime 𝔭 ≃ₐ[A₀] ↥ψₐ.range := AlgEquiv.ofInjective ψₐ hψinj
  have he : ∀ y, ((e y : ↥ψₐ.range) : R) = ψ y := fun y => rfl
  refine ⟨ψₐ.range, ?_, ?_, ?_, ?_⟩
  ·
    ext x
    rw [AlgHom.coe_range, Set.mem_range, Set.mem_ofPred_eq]
    constructor
    ·
      rintro ⟨y, rfl⟩
      obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl y
      refine ⟨(t : R), t.2, ((u : ↥T) : R), (u : ↥T).2, ?_, hψmk t u⟩
      refine fun hu => (Ideal.mem_primeCompl_iff.mp u.2) hu
    ·
      rintro ⟨t, ht, u, hu, hu𝔪, hx⟩
      have hu' : (⟨u, hu⟩ : ↥T) ∈ 𝔭.primeCompl := Ideal.mem_primeCompl_iff.mpr hu𝔪
      refine ⟨IsLocalization.mk' _ (⟨t, ht⟩ : ↥T) ⟨⟨u, hu⟩, hu'⟩, ?_⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hu𝔪
      apply hu𝔪.mul_left_inj.mp
      change ψ _ * u = x * u
      rw [hx]
      apply hψmk ⟨t, ht⟩ ⟨⟨u, hu⟩, hu'⟩
  ·
    apply isNoetherianRing_of_ringEquiv (Localization.AtPrime 𝔭) e.toRingEquiv
  ·
    apply IsLocalRing.of_surjective' e.toRingEquiv.toRingHom e.surjective
  ·
    intro x
    constructor
    ·
      intro hx
      apply hx.map ψₐ.range.val
    ·
      intro hx
      obtain ⟨y, rfl⟩ := e.surjective x
      obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl y
      rw [he] at hx
      have huR : IsUnit (((u : ↥T)) : R) := hM u
      have htR : IsUnit ((t : ↥T) : R) := by
        rw [← hψmk t u]
        apply hx.mul huR
      have ht : (t : ↥T) ∈ 𝔭.primeCompl := Ideal.mem_primeCompl_iff.mpr ((hunitR t).mpr htR)
      refine (IsUnit.of_mul_eq_one (b := IsLocalization.mk' (Localization.AtPrime 𝔭) (u : ↥T) ⟨t, ht⟩) ?_).map e
      rw [← IsLocalization.mk'_mul, mul_comm]
      apply IsLocalization.mk'_self


-- created on 2026-10-20
