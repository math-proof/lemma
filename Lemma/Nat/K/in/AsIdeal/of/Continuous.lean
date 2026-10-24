import Mathlib
import sympy.Basic
open NumberField IsDedekindDomain
open Filter Topology


/--
[NumberField_natCast_mem_asIdeal_of_continuous_ringHom_adicCompletion_padicAlgCl](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_natCast_mem_asIdeal_of_continuous_ringHom_adicCompletion_padicAlgCl.lean)
-/
@[path]
private lemma main
  [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime]
  {w : HeightOneSpectrum (𝓞 K)}
  {Φ : w.adicCompletion K →+* PadicAlgCl q}
-- given
  (hΦ : Continuous Φ) :
-- imply
  ((q : ℕ) : 𝓞 K) ∈ w.asIdeal := by
-- proof
  classical
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have : IsDomain (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.isDomain w.asIdeal
  let ℓ : ℕ := ringChar (𝓞 K ⧸ w.asIdeal)
  have hℓ0 : ℓ ≠ 0 := CharP.ringChar_ne_zero_of_finite (𝓞 K ⧸ w.asIdeal)
  have hℓ : ℓ.Prime := CharP.char_prime_of_ne_zero (𝓞 K ⧸ w.asIdeal) hℓ0
  have hℓw : ((ℓ : ℕ) : 𝓞 K) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, show ℓ = ringChar (𝓞 K ⧸ w.asIdeal) from rfl,
      ringChar.Nat.cast_ringChar]
  have hv : Valued.v (((ℓ : K)) : w.adicCompletion K) < 1 := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', show (ℓ : K) = algebraMap (𝓞 K) K (ℓ : 𝓞 K) from (map_natCast _ ℓ).symm,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem _ _).2 hℓw
  have hcoe : ((ℓ : K) : w.adicCompletion K) = ((ℓ : ℕ) : w.adicCompletion K) := by
    have h1 := map_natCast (algebraMap K (w.adicCompletion K)) ℓ
    rw [HeightOneSpectrum.algebraMap_adicCompletion] at h1
    simpa using h1
  have ht : Tendsto (fun n : ℕ => ((ℓ : ℕ) : w.adicCompletion K) ^ n) atTop (𝓝 0) := by
    rw [← hcoe]
    exact Valued.tendsto_zero_pow_of_v_lt_one hv
  have ht' : Tendsto (fun n : ℕ => ((ℓ : ℕ) : PadicAlgCl q) ^ n) atTop (𝓝 0) := by
    have h := (hΦ.tendsto 0).comp ht
    rw [map_zero] at h
    refine h.congr (fun n => ?_)
    simp [map_pow, map_natCast]
  have hnorm : ‖((ℓ : ℕ) : PadicAlgCl q)‖ < 1 := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht'
  have hnorm' : ‖((ℓ : ℕ) : ℚ_[q])‖ < 1 := by
    rw [← PadicAlgCl.norm_extends]
    simpa using hnorm
  have hdvd : q ∣ ℓ := Padic.norm_natCast_lt_one_iff.1 hnorm'
  have hq : q = ℓ := (Nat.prime_dvd_prime_iff_eq Fact.out hℓ).1 hdvd
  rwa [hq]


-- created on 2026-10-24
