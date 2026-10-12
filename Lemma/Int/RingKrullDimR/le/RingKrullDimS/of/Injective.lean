import Mathlib
import sympy.Basic


/--
[Algebra_IsIntegral_ringKrullDim_le_of_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsIntegral_ringKrullDim_le_of_injective.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
-- given
  (hinj : Function.Injective (algebraMap R S)) :
-- imply
  ringKrullDim R ≤ ringKrullDim S := by
-- proof
  classical
  obtain hR | hR := subsingleton_or_nontrivial R
  ·
    rw [ringKrullDim_eq_bot_of_subsingleton]
    apply bot_le
  have : Nontrivial S := hinj.nontrivial
  have hbot : ∀ P : Ideal R, (⊥ : Ideal S).under R ≤ P := by
    intro P x hx
    rw [Ideal.mem_under, Ideal.mem_bot] at hx
    have : x = 0 := hinj (by rw [hx, map_zero])
    rw [this]
    apply zero_mem
  have key : ∀ n : ℕ, ∀ l : LTSeries (PrimeSpectrum R), l.length = n →
      ∃ l' : LTSeries (PrimeSpectrum S), l'.length = n ∧
        l'.last.asIdeal.under R = l.last.asIdeal := by
    intro n
    induction n with
    | zero =>
      intro l hl
      obtain ⟨Q, -, hQ, hQc⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral l.last.asIdeal (⊥ : Ideal S) (hbot _)
      refine ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, ?_⟩
      simpa using hQc
    | succ n ih =>
      intro l hl
      have hne : l.length ≠ 0 := by
        omega
      obtain ⟨l'', hl'', hc⟩ := ih l.eraseLast (by simp [RelSeries.eraseLast_length, hl])
      have hrel : l.eraseLast.last < l.last := l.eraseLast_last_rel_last hne
      obtain ⟨Q, hQge, hQ, hQc⟩ :=
        Ideal.exists_ideal_over_prime_of_isIntegral l.last.asIdeal l''.last.asIdeal
          (by rw [hc]; exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr hrel.le)
      have hlt : l''.last < ⟨Q, hQ⟩ := by
        refine lt_of_le_of_ne ((PrimeSpectrum.asIdeal_le_asIdeal _ _).mp hQge) ?_
        intro heq
        apply (ne_of_lt hrel)
        apply PrimeSpectrum.ext
        rw [← hc, ← hQc, heq]
      refine ⟨l''.snoc ⟨Q, hQ⟩ hlt, ?_, ?_⟩
      · simp [RelSeries.snoc_length, hl'']
      · simpa [RelSeries.last_snoc] using hQc
  rw [ringKrullDim, ringKrullDim, Order.krullDim_eq_iSup_length, Order.krullDim_eq_iSup_length]
  refine WithBot.coe_le_coe.mpr (iSup_le fun l => ?_)
  obtain ⟨l', hl', -⟩ := key l.length l rfl
  apply le_iSup_of_le l' (by rw [hl'])


-- created on 2026-10-12
