import Mathlib
import sympy.Basic


/--
[IsDiscreteValuationRing_exists_pow_mul_mem_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_exists_pow_mul_mem_range.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  {t : R}
  {x : K}
-- given
  (ht : t ≠ 0)
  (ht' : t ∈ IsLocalRing.maximalIdeal R) :
-- imply
  ∃ N : ℕ, ∃ r : R, algebraMap R K r = algebraMap R K t ^ N * x := by
-- proof
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ht hϖ
  have hn1 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (IsLocalRing.mem_maximalIdeal _).mp ht' (hn.symm.isUnit isUnit_one)
  have hdvd : b ∣ t ^ m := by
    have h1 : b ∣ ϖ ^ m := hm.dvd
    have h2 : ϖ ^ m ∣ ϖ ^ (n * m) :=
      pow_dvd_pow ϖ (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hn1))
    have h3 : ϖ ^ (n * m) ∣ t ^ m := by
      rw [pow_mul]
      exact pow_dvd_pow_of_dvd hn.symm.dvd m
    exact h1.trans (h2.trans h3)
  obtain ⟨c, hc⟩ := hdvd
  refine ⟨m, c * a, ?_⟩
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  rw [← map_pow, hc, map_mul, map_mul]
  field_simp


-- created on 2026-10-05
