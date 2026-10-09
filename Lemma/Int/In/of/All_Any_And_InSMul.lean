import Mathlib
import sympy.Basic


/--
[Submodule_mem_of_forall_prime_exists_smul_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_mem_of_forall_prime_exists_smul_mem.lean)
-/
@[path]
private lemma main
  [AddCommGroup V]
  {M : Submodule ℤ V}
  {x : V}
-- given
  (h : ∀ ℓ : ℕ, ℓ.Prime → ∃ s : ℤ, ¬ (ℓ : ℤ) ∣ s ∧ s • x ∈ M) :
-- imply
  x ∈ M := by
-- proof
  let I : Ideal ℤ := M.comap (LinearMap.toSpanSingleton ℤ V x)
  have hI : ∀ n : ℤ, n ∈ I ↔ n • x ∈ M := fun n => by
    change LinearMap.toSpanSingleton ℤ V x n ∈ M ↔ _
    rw [LinearMap.toSpanSingleton_apply]
  obtain ⟨d, hd⟩ := (IsPrincipalIdealRing.principal I).principal
  have hdI : ∀ n : ℤ, n ∈ I ↔ d ∣ n := fun n => by
    rw [hd]
    exact Ideal.mem_span_singleton
  by_cases h1 : d.natAbs = 1
  · have h1' : (1 : ℤ) ∈ I := (hdI 1).2 (Int.isUnit_iff_natAbs_eq.mpr h1).dvd
    have h1'' := (hI 1).1 h1'
    rwa [one_smul] at h1''
  · obtain ⟨ℓ, hℓp, hℓd⟩ := Int.exists_prime_and_dvd h1
    obtain ⟨s, hs, hsx⟩ := h ℓ.natAbs (Int.prime_iff_natAbs_prime.mp hℓp)
    exact (hs (Int.natAbs_dvd.mpr (hℓd.trans ((hdI s).1 ((hI s).2 hsx))))).elim


-- created on 2026-10-05
