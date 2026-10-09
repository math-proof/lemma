import Mathlib
import sympy.Basic

open IsDedekindDomain NumberField

/--
[IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal.lean)
-/

private lemma  natCast_mem_asIdeal_iff' (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

private lemma  natGenerator_eq_of_prime_mem' {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : Rat.HeightOneSpectrum.natGenerator v = p :=
  (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).1
    ((natCast_mem_asIdeal_iff' v p).1 hv)
@[path]
private lemma main
  {r : ℕ}
  {v w : HeightOneSpectrum (𝓞 ℚ)}
-- given
  (hr : r.Prime)
  (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
  (hw : ((r : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) :
-- imply
  w = v := by
-- proof
  have e1 := natGenerator_eq_of_prime_mem' hr w hw
  have e2 := natGenerator_eq_of_prime_mem' hr v hv
  have : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w = Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v :=
    Subtype.ext (e1.trans e2.symm)
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective this


-- created on 2026-10-05
