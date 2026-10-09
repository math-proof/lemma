import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalRing_exists_dvd_pow_of_krullDimLE_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_dvd_pow_of_krullDimLE_one.lean)
-/

private lemma  exists_dvd_pow {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
    {b : R} (hb : b ≠ 0) {c : R} (hc : c ∈ maximalIdeal R) : ∃ n : ℕ, b ∣ c ^ n := by
  by_cases hu : IsUnit b
  · exact ⟨0, hu.dvd⟩
  · have hne : Ideal.span {b} ≠ ⊤ := by
      rwa [Ne, Ideal.span_singleton_eq_top]
    have hrad : (Ideal.span {b}).radical = maximalIdeal R := by
      rw [Ideal.radical_eq_sInf]
      refine le_antisymm (sInf_le ⟨IsLocalRing.le_maximalIdeal hne, inferInstance⟩) (le_sInf ?_)
      rintro J ⟨hJ, hJp⟩
      have hJ0 : J ≠ ⊥ := by
        intro h0
        rw [h0, Ideal.span_singleton_le_iff_mem, Ideal.mem_bot] at hJ
        exact hb hJ
      exact (IsLocalRing.eq_maximalIdeal (hJp.isMaximal_of_ne_bot hJ0)).ge
    have hc' : c ∈ (Ideal.span {b}).radical := hrad ▸ hc
    obtain ⟨n, hn⟩ := hc'
    exact ⟨n, Ideal.mem_span_singleton.mp hn⟩
@[path]
private lemma main
  [CommRing R] [IsDomain R] [IsLocalRing R] [Ring.KrullDimLE 1 R]
  {b : R}
  {c : R}
-- given
  (hb : b ≠ 0)
  (hc : c ∈ IsLocalRing.maximalIdeal R) :
-- imply
  ∃ n : ℕ, b ∣ c ^ n :=
-- proof
  exists_dvd_pow hb hc


-- created on 2026-10-05
