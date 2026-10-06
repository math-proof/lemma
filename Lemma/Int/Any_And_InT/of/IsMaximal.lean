import Mathlib
import sympy.Basic

open Ideal

/--
[Ideal_exists_prime_natCast_mem_of_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_prime_natCast_mem_of_isMaximal.lean)
-/
@[main]
private lemma main
  [CommRing T] [Module.Finite ℤ T]
  {𝔪 : Ideal T}
-- given
  (h𝔪 : 𝔪.IsMaximal) :
-- imply
  ∃ p : ℕ, p.Prime ∧ (p : T) ∈ 𝔪 := by
-- proof
  classical
  haveI := h𝔪
  haveI : Algebra.IsIntegral ℤ T := inferInstance
  have hmax : (𝔪.comap (algebraMap ℤ T)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal 𝔪
  set P := 𝔪.comap (algebraMap ℤ T) with hP
  obtain ⟨n, hn⟩ : ∃ n : ℤ, P = Ideal.span {n} :=
    ⟨Submodule.IsPrincipal.generator P, (Ideal.span_singleton_generator P).symm⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    have hbot : P = ⊥ := by simpa using hn
    exact Ring.ne_bot_of_isMaximal_of_not_isField hmax Int.not_isField hbot
  have hprime : Prime n := (Ideal.span_singleton_prime hn0).mp (hn ▸ hmax.isPrime)
  refine ⟨n.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_⟩
  have hmemP : (n.natAbs : ℤ) ∈ P := by
    rw [hn, Ideal.mem_span_singleton]
    exact Int.dvd_natAbs_self
  have := Ideal.mem_comap.mp hmemP
  simpa using this


-- created on 2026-10-05
