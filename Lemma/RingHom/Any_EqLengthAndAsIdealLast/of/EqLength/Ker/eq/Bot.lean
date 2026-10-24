import Mathlib
import sympy.Basic


/--
[exists_lifted_prime_chain](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/IntegralDim.lean)
-/
@[path]
private lemma main
  [CommRing R]
  [CommRing S]
  [Algebra R S]
  [Algebra.IsIntegral R S]
  {n : ℕ}
  {s : LTSeries (PrimeSpectrum R)}
-- given
  (hker : RingHom.ker (algebraMap R S) = ⊥)
  (hs : s.length = n) :
-- imply
  ∃ t : LTSeries (PrimeSpectrum S),
    t.length = n ∧ (t.last).asIdeal.comap (algebraMap R S) = (s.last).asIdeal := by
-- proof
  induction n generalizing s with
  | zero =>
    have hp := (s.last).isPrime
    obtain ⟨Q, -, hQp, hQeq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (s.last).asIdeal (⊥ : Ideal S)
      (by simp [Ideal.under, ← RingHom.ker_eq_comap_bot, hker])
    refine ⟨RelSeries.singleton _ ⟨Q, hQp⟩, ?_, ?_⟩
    · rfl
    · simpa [RelSeries.last_singleton, Ideal.under_def] using hQeq
  | succ n ih =>
    have hlen_pos : s.length ≠ 0 := by omega
    let s' := s.eraseLast
    have hs'_len : s'.length = n := by simp [s', RelSeries.eraseLast, hs]
    obtain ⟨t', ht'_len, ht'_comap⟩ := ih (s := s') hs'_len
    have hlt_chain : s'.last < s.last := s.eraseLast_last_rel_last hlen_pos
    have hunder_le : (t'.last).asIdeal.under R ≤ (s.last).asIdeal := by
      rw [Ideal.under_def, ht'_comap]
      apply le_of_lt hlt_chain
    have hp := (s.last).isPrime
    obtain ⟨Qnew, hQge, hQp, hQeq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (s.last).asIdeal (t'.last).asIdeal hunder_le
    have hlt_new : t'.last < (⟨Qnew, hQp⟩ : PrimeSpectrum S) := by
      refine lt_of_le_of_ne hQge ?_
      intro heq
      have heq' : (t'.last).asIdeal = Qnew := PrimeSpectrum.ext_iff.mp heq
      rw [← heq', Ideal.under_def, ht'_comap] at hQeq
      apply absurd (PrimeSpectrum.ext_iff.mpr hQeq) (ne_of_lt hlt_chain)
    refine ⟨t'.snoc ⟨Qnew, hQp⟩ hlt_new, ?_, ?_⟩
    · simp [ht'_len]
    ·
      rw [RelSeries.last_snoc]
      simpa [Ideal.under_def] using hQeq


-- created on 2026-10-23
-- updated on 2026-10-24
