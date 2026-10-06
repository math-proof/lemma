import Mathlib
import sympy.Basic


/--
[Ideal_finite_setOf_height_eq_one_and_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_finite_setOf_height_eq_one_and_mem.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {b : R}
-- given
  (hb : b ≠ 0) :
-- imply
  {p : Ideal R | p.IsPrime ∧ p.height = 1 ∧ b ∈ p}.Finite := by
-- proof
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {b})).subset ?_
  rintro p ⟨hp, hh, hbp⟩
  haveI := hp
  have hle : Ideal.span {b} ≤ p := (Ideal.span_singleton_le_iff_mem _).mpr hbp
  refine ⟨⟨hp, hle⟩, fun q ⟨hq, hbq⟩ hqp => ?_⟩

  set S := Localization.AtPrime p
  have hdim : ringKrullDim S = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S, hh]
    norm_cast
  have hKDL : Ring.KrullDimLE 1 S :=
    Ring.krullDimLE_iff.mpr (le_of_eq (by rw [hdim, Nat.cast_one]))
  have hmax : ∀ P : Ideal S, P ≠ ⊥ → P.IsPrime → P.IsMaximal :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hKDL
  have hdisj : Disjoint (p.primeCompl : Set R) q :=
    Set.disjoint_left.mpr fun x hx hxq => hx (hqp hxq)
  have hqS : (Ideal.map (algebraMap R S) q).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl S q hq hdisj
  have hqS0 : Ideal.map (algebraMap R S) q ≠ ⊥ := by
    intro hbot
    have hbS : algebraMap R S b ∈ Ideal.map (algebraMap R S) q :=
      Ideal.mem_map_of_mem _ (hbq (Ideal.subset_span rfl))
    rw [hbot, Ideal.mem_bot] at hbS
    exact hb ((IsLocalization.injective S p.primeCompl_le_nonZeroDivisors) (by rw [hbS, map_zero]))
  have hqmax : Ideal.map (algebraMap R S) q = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal (hmax _ hqS0 hqS)
  have hq' : q = p := by
    rw [← IsLocalization.comap_map_of_isPrime_disjoint p.primeCompl S hq hdisj, hqmax,
      Localization.AtPrime.comap_maximalIdeal]
  exact hq'.ge


-- created on 2026-10-05
