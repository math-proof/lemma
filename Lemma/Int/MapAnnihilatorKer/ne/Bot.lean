import Mathlib
import sympy.Basic

open IsLocalRing

/--
[AlgHom_congruenceIdeal_ne_bot_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_congruenceIdeal_ne_bot_of_isReduced.lean)
-/
@[path]
private lemma main
  {𝒪 : Type u} [CommRing 𝒪] [IsDomain 𝒪]
  {T : Type v} [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsNoetherianRing T] [IsReduced T]
  {πT : T →ₐ[𝒪] 𝒪} :
-- imply
  (RingHom.ker πT).annihilator.map πT ≠ ⊥ := by
-- proof
  classical
  set 𝔭 : Ideal T := RingHom.ker πT with h𝔭def
  have h𝔭prime : 𝔭.IsPrime := RingHom.ker_isPrime πT

  have hcomap : 𝔭.comap (algebraMap 𝒪 T) = ⊥ := by
    refine le_bot_iff.mp fun a ha => ?_
    rw [Ideal.mem_comap, h𝔭def, RingHom.mem_ker] at ha
    have ha' : πT (algebraMap 𝒪 T a) = 0 := ha
    rw [AlgHom.commutes] at ha'
    exact (Ideal.mem_bot).mpr ha'

  have hmin : 𝔭 ∈ minimalPrimes T := by
    refine ⟨⟨h𝔭prime, bot_le⟩, ?_⟩
    rintro Q ⟨hQ, -⟩ hQle
    by_contra hnot
    obtain ⟨x, hx𝔭, hxQ⟩ := SetLike.not_le_iff_exists.mp hnot
    have := hQ
    have hlt := Ideal.under_lt_under_of_integral_mem_sdiff (R := 𝒪) hQle ⟨hx𝔭, hxQ⟩
      (Algebra.IsIntegral.isIntegral x)
    simp only [Ideal.under_def, hcomap] at hlt
    exact not_lt_bot hlt

  have hfin : (minimalPrimes T).Finite := minimalPrimes.finite_of_isNoetherianRing T
  set s : Finset (Ideal T) := hfin.toFinset.erase 𝔭 with hsdef
  set I : Ideal T := s.inf id with hIdef
  have hI_ann : I ≤ 𝔭.annihilator := by
    intro t ht
    refine Submodule.mem_annihilator.mpr fun x hx => ?_
    have hmem : t * x ∈ sInf (minimalPrimes T) := by
      refine Submodule.mem_sInf.mpr fun Q hQ => ?_
      by_cases hQ𝔭 : Q = 𝔭
      · subst hQ𝔭; exact Ideal.mul_mem_left _ t hx
      · have hQs : Q ∈ s := Finset.mem_erase.mpr ⟨hQ𝔭, hfin.mem_toFinset.mpr hQ⟩
        have htQ : t ∈ Q := by
          have := (Finset.inf_le (f := id) hQs : I ≤ id Q) ht
          exact this
        exact Ideal.mul_mem_right x Q htQ
    have hnil : sInf (minimalPrimes T) = (⊥ : Ideal T) := by
      have h := Ideal.sInf_minimalPrimes (I := (⊥ : Ideal T))
      have h0 : (⊥ : Ideal T).radical = ⊥ := nilradical_eq_zero T
      rw [h0] at h
      exact h
    rw [hnil, Ideal.mem_bot] at hmem
    simpa [smul_eq_mul] using hmem

  have hI_not_le : ¬ I ≤ 𝔭 := by
    intro hle
    rcases s.eq_empty_or_nonempty with hs | hs
    · have hItop : I = ⊤ := by rw [hIdef, hs, Finset.inf_empty]
      exact h𝔭prime.ne_top (top_le_iff.mp (hItop ▸ hle))
    · obtain ⟨Q, hQs, hQle⟩ := (h𝔭prime.inf_le' (s := s) (f := id)).mp hle
      obtain ⟨hQ𝔭, hQmin⟩ := Finset.mem_erase.mp hQs
      have hQmin' : Q ∈ minimalPrimes T := hfin.mem_toFinset.mp hQmin
      have h𝔭leQ : 𝔭 ≤ Q := hmin.2 ⟨hQmin'.1.1, bot_le⟩ hQle
      exact hQ𝔭 (le_antisymm hQle h𝔭leQ)

  obtain ⟨t, htI, ht𝔭⟩ := SetLike.not_le_iff_exists.mp hI_not_le
  intro hbot
  have hmem : πT t ∈ (RingHom.ker πT).annihilator.map πT := Ideal.mem_map_of_mem _ (hI_ann htI)
  rw [hbot, Ideal.mem_bot] at hmem
  exact ht𝔭 (by rw [h𝔭def, RingHom.mem_ker]; exact hmem)


-- created on 2026-10-09
