import Mathlib
import sympy.Basic


/--
[DeligneSerre_exists_minimalPrime_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_DeligneSerre_exists_minimalPrime_le.lean)
-/
@[main]
private lemma main
  [CommRing T] [Module.Finite ℤ T] [Module.IsTorsionFree ℤ T]
  {𝔪 : Ideal T}
-- given
  (h𝔪 : 𝔪.IsPrime) :
-- imply
  ∃ 𝔭 ∈ minimalPrimes T, 𝔭 ≤ 𝔪 ∧ ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0 := by
-- proof
  haveI := h𝔪
  haveI : 𝔪.LiesOver (𝔪.under ℤ) := ⟨rfl⟩
  haveI : (𝔪.under ℤ).IsPrime := Ideal.IsPrime.under ℤ 𝔪
  obtain ⟨P, hP𝔪, hPprime, hPover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal ℤ)) (q := 𝔪.under ℤ) 𝔪 bot_le
  haveI := hPprime
  obtain ⟨𝔭, h𝔭min, h𝔭P⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal T)) (J := P) bot_le
  refine ⟨𝔭, h𝔭min, h𝔭P.trans hP𝔪, fun n hn => ?_⟩
  have hnP : algebraMap ℤ T n ∈ P := h𝔭P hn
  have : n ∈ P.under ℤ := hnP
  rw [← hPover.over] at this
  simpa using this


-- created on 2026-10-05
