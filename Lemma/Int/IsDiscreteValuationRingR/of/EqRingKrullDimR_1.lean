import Mathlib
import sympy.Basic


/--
[IsDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one.lean)
-/

private lemma  IsDiscreteValuationRing.of_isIntegrallyClosed_of_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
    (h : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hnf : ¬ IsField R := fun hf => by
    have h0 := ringKrullDim_eq_zero_of_isField hf
    rw [h] at h0
    exact one_ne_zero h0
  have hdim : Ring.DimensionLEOne R := by
    refine ⟨fun {p} hp hpp => ?_⟩
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hpp.ne_top
    by_contra hnot
    have hlt : p < m := lt_of_le_of_ne hpm (fun e => hnot (e ▸ hm))
    have hmh : (m.height : WithBot ℕ∞) ≤ 1 := by
      rw [← h]
      exact (ringKrullDim_le_iff_isMaximal_height_le (ringKrullDim R)).mp le_rfl hm
    have hmh' : m.height ≤ (1 : ℕ) := by exact_mod_cast hmh
    rw [Ideal.height_le_iff] at hmh'
    have hp0 : p.height = 0 := by
      exact Order.lt_one_iff.mp (hmh' p hpp hlt)
    rw [Ideal.height_eq_zero_iff] at hp0
    exact hp (le_bot_iff.mp (hp0.2 ⟨Ideal.isPrime_bot, le_rfl⟩ bot_le))
  have hded : IsDedekindRing R := IsDedekindRing.mk
  have hdd : IsDedekindDomain R := IsDedekindDomain.mk
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 1 3).mpr hdd
@[path]
private lemma main
  [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
-- given
  (h : ringKrullDim R = 1) :
-- imply
  IsDiscreteValuationRing R :=
-- proof
  IsDiscreteValuationRing.of_isIntegrallyClosed_of_ringKrullDim_eq_one R h


-- created on 2026-10-05
