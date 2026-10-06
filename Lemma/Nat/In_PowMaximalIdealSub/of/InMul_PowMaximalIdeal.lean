import Mathlib
import sympy.Basic


/--
[IsDiscreteValuationRing_mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem.lean)
-/
@[main]
private lemma main
  [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  {a v : 𝒪}
  {k M : ℕ}
-- given
  (hk : a ∉ IsLocalRing.maximalIdeal 𝒪 ^ (k + 1))
  (h : a * v ∈ IsLocalRing.maximalIdeal 𝒪 ^ M) :
-- imply
  v ∈ IsLocalRing.maximalIdeal 𝒪 ^ (M - k) := by
-- proof
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hk h ⊢

  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hk (dvd_zero _)
  by_cases hv0 : v = 0
  · rw [hv0]; exact dvd_zero _

  obtain ⟨i, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨j, u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 hϖ

  have hik : i ≤ k := by
    by_contra hlt
    exact hk (dvd_mul_of_dvd_right (pow_dvd_pow ϖ (by omega)) _)

  have hM : M ≤ i + j := by
    have h' : ϖ ^ M ∣ ϖ ^ (i + j) := by
      rw [show (u : 𝒪) * ϖ ^ i * ((u' : 𝒪) * ϖ ^ j) = ((u * u' : 𝒪ˣ) : 𝒪) * ϖ ^ (i + j) by
        rw [Units.val_mul, pow_add]; ring] at h
      exact (Units.isUnit (u * u')).dvd_mul_left.mp h
    exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).mp h'
  exact dvd_mul_of_dvd_right (pow_dvd_pow ϖ (by omega)) _


-- created on 2026-10-05
