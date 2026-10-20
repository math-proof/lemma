import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma exists_mem_map_eq_span_singleton
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : R →+* S) (P : Ideal R) :
    ∃ a ∈ P, Ideal.map f P = Ideal.span {f a} := by
  classical
  by_cases hbot : Ideal.map f P = ⊥
  · exact ⟨0, P.zero_mem, by rw [hbot, map_zero, Ideal.span_singleton_eq_bot.mpr rfl]⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hbot hϖ
  have hex : ∃ x ∈ P, f x ∉ Ideal.span {ϖ ^ (n + 1)} := by
    by_contra h
    push Not at h
    have hle : Ideal.map f P ≤ Ideal.span {ϖ ^ (n + 1)} := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      exact h x hx
    rw [hn, Ideal.span_singleton_le_span_singleton, pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit] at hle
    omega
  obtain ⟨x, hxP, hx⟩ := hex
  have hxn : f x ∈ Ideal.span {ϖ ^ n} := hn ▸ Ideal.mem_map_of_mem f hxP
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hxn
  have hcu : IsUnit c := by
    by_contra hcu
    have hcm : c ∈ IsLocalRing.maximalIdeal S := hcu
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hcm
    obtain ⟨d, rfl⟩ := hcm
    apply hx
    rw [← hc, Ideal.mem_span_singleton']
    exact ⟨d, by ring⟩
  refine ⟨x, hxP, ?_⟩
  rw [hn, ← hc, Ideal.span_singleton_mul_left_unit hcu]
/--
[Ideal_isPrincipal_of_surjective_of_isDiscreteValuationRing_of_ker_eq_span_singleton_of_forall_mul_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_isPrincipal_of_surjective_of_isDiscreteValuationRing_of_ker_eq_span_singleton_of_forall_mul_mem.lean)
-/
@[path]
private lemma main
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : R →+* S) (hf : Function.Surjective f) (t : R) (hker : RingHom.ker f = Ideal.span {t})
    (P : Ideal R) (hP : ∀ r : R, t * r ∈ P → r ∈ P) :
    Submodule.IsPrincipal P := by
  classical
  have hfg : P.FG := IsNoetherian.noetherian P
  have htm : t ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : (1 : R) ∈ RingHom.ker f := by
      rw [hker, Ideal.span_singleton_eq_top.mpr hu]
      trivial
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨a, haP, ha⟩ := exists_mem_map_eq_span_singleton f P
  have hle : P ≤ Ideal.span {a} ⊔ IsLocalRing.maximalIdeal R • P := by
    intro x hx
    have hfx : f x ∈ Ideal.span {f a} := ha ▸ Ideal.mem_map_of_mem f hx
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hfx
    obtain ⟨r, rfl⟩ := hf c
    have hk : x - r * a ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, map_sub, map_mul, hc, sub_self]
    rw [hker, Ideal.mem_span_singleton'] at hk
    obtain ⟨y, hy⟩ := hk
    have hyP : y ∈ P := hP y (by rw [mul_comm, hy]; exact P.sub_mem hx (P.mul_mem_left r haP))
    have hxe : x = r * a + t * y := by rw [mul_comm t, hy]; ring
    rw [hxe]
    exact Submodule.add_mem_sup (Ideal.mem_span_singleton'.mpr ⟨r, rfl⟩)
      (Submodule.smul_mem_smul htm hyP)
  have hPa : P ≤ Ideal.span {a} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle
  exact ⟨a, le_antisymm hPa ((Ideal.span_singleton_le_iff_mem P).mpr haP)⟩

-- created on 2026-10-20
