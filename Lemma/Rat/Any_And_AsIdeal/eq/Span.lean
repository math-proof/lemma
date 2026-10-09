import Mathlib
import sympy.Basic

open IsDedekindDomain NumberField

/--
[IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat.lean)
-/
@[path]
private lemma main
  {v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)} :
-- imply
  ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
-- proof
  refine ⟨Rat.HeightOneSpectrum.natGenerator v, Rat.HeightOneSpectrum.prime_natGenerator v, ?_⟩
  set e : 𝓞 ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) with he
  have h : Ideal.map (e : 𝓞 ℚ →+* ℤ) v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} :=
    (Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v).symm
  have h3 : Ideal.map (e.symm : ℤ →+* 𝓞 ℚ) (Ideal.map (e : 𝓞 ℚ →+* ℤ) v.asIdeal) = v.asIdeal :=
    Ideal.map_of_equiv e
  rw [← h3, h, Ideal.map_span, Set.image_singleton]
  congr 2
  simp


-- created on 2026-10-05
