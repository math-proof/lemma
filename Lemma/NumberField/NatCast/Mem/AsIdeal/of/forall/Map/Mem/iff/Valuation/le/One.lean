import Mathlib
import sympy.Basic

open NumberField IsDedekindDomain

/--
[NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one.lean)
-/
@[path]
private lemma main
  [Field K] [NumberField K] [Field Ω]
  {σ : K →+* Ω}
  {A : ValuationSubring Ω}
  {v : HeightOneSpectrum (𝓞 K)}
  {p : ℕ}
-- given
  (hv : ∀ x : K, σ x ∈ A ↔ v.valuation K x ≤ 1)
  (hp : A.valuation (σ (p : K)) < 1) :
-- imply
  ((p : ℤ) : 𝓞 K) ∈ v.asIdeal := by
-- proof
  have hcast : algebraMap (𝓞 K) K ((p : ℤ) : 𝓞 K) = (p : K) := by
    rw [map_intCast, Int.cast_natCast]
  by_cases hp0 : (p : K) = 0
  ·
    have : ((p : ℤ) : 𝓞 K) = 0 :=
      (map_eq_zero_iff (algebraMap (𝓞 K) K) (IsFractionRing.injective (𝓞 K) K)).mp
        (hcast.trans hp0)
    rw [this]
    exact Ideal.zero_mem _

  have hσp0 : σ (p : K) ≠ 0 := (map_ne_zero σ).mpr hp0
  have hnot : σ ((p : K)⁻¹) ∉ A := by
    intro hmem
    rw [map_inv₀, ← A.valuation_le_one_iff, map_inv₀,
      inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hσp0))] at hmem
    exact absurd hp (not_lt.mpr hmem)
  rw [hv, not_le, ← hcast, map_inv₀] at hnot

  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  have hne : v.valuation K (algebraMap (𝓞 K) K ((p : ℤ) : 𝓞 K)) ≠ 0 := by
    rw [Valuation.ne_zero_iff, hcast]
    exact hp0
  exact (one_lt_inv₀ (zero_lt_iff.mpr hne)).mp hnot


-- created on 2026-10-05
