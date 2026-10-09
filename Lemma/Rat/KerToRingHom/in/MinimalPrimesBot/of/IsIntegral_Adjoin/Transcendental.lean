import Mathlib
import sympy.Basic


/--
[AlgHom_ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_ker_mem_minimalPrimes_of_transcendental_of_isIntegral_adjoin_singleton.lean)
-/
@[path]
private lemma main
  {A₀ R K : Type} [CommRing A₀] [CommRing R] [Field K] [Algebra A₀ R] [Algebra A₀ K]
  {j₀ : R}
  {ι : R →ₐ[A₀] K}
-- given
  (htr : Transcendental A₀ (ι j₀))
  (hint : Algebra.IsIntegral ↥(Algebra.adjoin A₀ {j₀}) R) :
-- imply
  RingHom.ker ι.toRingHom ∈ (⊥ : Ideal R).minimalPrimes := by
-- proof
  classical
  set R0 : Subalgebra A₀ R := Algebra.adjoin A₀ {j₀} with hR0
  have hR0f : ∀ r : ↥R0, ∃ f : Polynomial A₀, Polynomial.aeval j₀ f = (r : R) := by
    intro r
    have : (r : R) ∈ (Polynomial.aeval (R := A₀) j₀).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact r.2
    exact this

  have hcomap : Ideal.under (↥R0) (RingHom.ker ι.toRingHom) = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    rw [Ideal.mem_under, RingHom.mem_ker] at hr
    rw [Ideal.mem_bot]
    obtain ⟨f, hf⟩ := hR0f r
    have hf0 : Polynomial.aeval (ι j₀) f = 0 := by
      rw [Polynomial.aeval_algHom_apply, hf]; exact hr
    have hf00 : f = 0 := (transcendental_iff.mp htr) _ hf0
    apply Subtype.ext
    show (r : R) = 0
    rw [← hf, hf00, map_zero]

  have hprime : (RingHom.ker ι.toRingHom).IsPrime := RingHom.ker_isPrime _
  refine ⟨⟨hprime, bot_le⟩, ?_⟩
  rintro 𝔮 ⟨h𝔮, -⟩ hle
  by_contra hnot
  obtain ⟨x, hxp, hxq⟩ := Set.not_subset.mp hnot
  have := h𝔮
  have hlt := Ideal.under_lt_under_of_integral_mem_sdiff (R := ↥R0) hle ⟨hxp, hxq⟩ (hint.isIntegral x)
  rw [hcomap] at hlt
  exact not_lt_bot hlt


-- created on 2026-10-05
