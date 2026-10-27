import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma exists_mem_map_eq_span_singleton
  [CommRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  (f : R →+* S)
  (P : Ideal R) :
  -- imply
  ∃ a ∈ P, Ideal.map f P = Ideal.span {f a} := by
  -- proof
  classical
  if hbot : Ideal.map f P = ⊥ then
    exact ⟨0, P.zero_mem, by rw [hbot, map_zero, Iff.mpr Ideal.span_singleton_eq_bot rfl]⟩
  else
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hbot hϖ
    have hex : ∃ x ∈ P, f x ∉ Ideal.span {ϖ ^ (n + 1)} := by
      by_contra h
      push Not at h
      have hle : Ideal.map f P ≤ Ideal.span {ϖ ^ (n + 1)} := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        apply h x hx
      rw [hn, Ideal.span_singleton_le_span_singleton, pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit] at hle
      omega
    obtain ⟨x, hxP, hx⟩ := hex
    have hxn : f x ∈ Ideal.span {ϖ ^ n} := hn ▸ Ideal.mem_map_of_mem f hxP
    obtain ⟨c, hc⟩ := Iff.mp Ideal.mem_span_singleton' hxn
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
  [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  (f : R →+* S)
  (hf : Function.Surjective f)
  (t : R)
  (hker : RingHom.ker f = Ideal.span {t})
  (P : Ideal R)
  (hP : ∀ r : R, t * r ∈ P → r ∈ P) :
  -- imply
  Submodule.IsPrincipal P := by
  -- proof
  classical
  have hfg : P.FG := IsNoetherian.noetherian P
  have htm : t ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 : (1 : R) ∈ RingHom.ker f := by
      rw [hker, Iff.mpr Ideal.span_singleton_eq_top hu]
      trivial
    rw [RingHom.mem_ker, map_one] at h1
    apply one_ne_zero h1
  obtain ⟨a, haP, ha⟩ := exists_mem_map_eq_span_singleton f P
  have hle : P ≤ Ideal.span {a} ⊔ IsLocalRing.maximalIdeal R • P := by
    intro x hx
    have hfx : f x ∈ Ideal.span {f a} := ha ▸ Ideal.mem_map_of_mem f hx
    obtain ⟨c, hc⟩ := Iff.mp Ideal.mem_span_singleton' hfx
    obtain ⟨r, rfl⟩ := hf c
    have hk : x - r * a ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, map_sub, map_mul, hc, sub_self]
    rw [hker, Ideal.mem_span_singleton'] at hk
    obtain ⟨y, hy⟩ := hk
    have hyP : y ∈ P := by
      apply hP y
      rw [mul_comm, hy]
      apply P.sub_mem hx (P.mul_mem_left r haP)
    have hxe : x = r * a + t * y := by
      rw [mul_comm t, hy]
      ring
    rw [hxe]
    apply Submodule.add_mem_sup (Iff.mpr Ideal.mem_span_singleton' ⟨r, rfl⟩) (Submodule.smul_mem_smul htm hyP)
  suffices hPa : P ≤ Ideal.span {a} by
    exact ⟨a, le_antisymm hPa (Iff.mpr (Ideal.span_singleton_le_iff_mem P) haP)⟩
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson ⊥) hle


-- created on 2026-10-20
