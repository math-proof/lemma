import Mathlib
import sympy.Basic


/--
[IsIntegrallyClosed_exists_algebraMap_eq_of_isIntegral_pow_mul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsIntegrallyClosed_exists_algebraMap_eq_of_isIntegral_pow_mul.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
  {t : R}
  {f : K}
-- given
  (ht0 : t ≠ 0)
  (ht : (Ideal.span {t}).IsPrime)
  (hv : ∃ r s : R, s ∉ Ideal.span {t} ∧ f * algebraMap R K s = algebraMap R K r)
  (hint : ∃ n : ℕ, IsIntegral R (algebraMap R K t ^ n * f)) :
-- imply
  ∃ r : R, algebraMap R K r = f := by
-- proof
  obtain ⟨n, hn⟩ := hint
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  obtain ⟨r, s, hs, hfs⟩ := hv
  have htK : algebraMap R K t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ht0
  have hprime : Prime t := (Ideal.span_singleton_prime ht0).mp ht
  have hts : ¬ t ∣ s := fun h => hs (Ideal.mem_span_singleton.mpr h)

  have has : a * s = t ^ n * r := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, map_pow, ha, mul_assoc, hfs]

  obtain ⟨c, hc⟩ := hprime.pow_dvd_of_dvd_mul_right n hts ⟨r, has⟩
  refine ⟨c, mul_left_cancel₀ (pow_ne_zero n htK) ?_⟩
  rw [← ha, hc, map_mul, map_pow]


-- created on 2026-10-05
