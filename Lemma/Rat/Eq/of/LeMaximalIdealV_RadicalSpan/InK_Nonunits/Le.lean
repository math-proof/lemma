import Mathlib
import sympy.Basic


/--
[ValuationSubring_eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_eq_of_le_of_mem_nonunits_of_maximalIdeal_le_radical.lean)
-/
@[main]
private lemma main
  [Field K]
  {V W : ValuationSubring K}
  {x : ↥V}
-- given
  (hVW : V ≤ W)
  (hxW : (x : K) ∈ W.nonunits)
  (hrad : IsLocalRing.maximalIdeal ↥V ≤ (Ideal.span {x}).radical) :
-- imply
  V = W := by
-- proof
  have hxP : x ∈ V.idealOfLE W hVW := by
    have h1 : ((V.inclusion W hVW x : ↥W) : K) ∈ W.nonunits := hxW
    exact Ideal.mem_comap.mpr (ValuationSubring.coe_mem_nonunits_iff.mp h1)
  have hle : IsLocalRing.maximalIdeal ↥V ≤ V.idealOfLE W hVW := by
    refine le_trans hrad ?_
    refine (Ideal.IsPrime.radical_le_iff inferInstance).mpr ?_
    exact (Ideal.span_singleton_le_iff_mem _).mpr hxP
  have heq : V.idealOfLE W hVW = IsLocalRing.maximalIdeal ↥V :=
    le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) hle
  have key : ∀ (P : Ideal ↥V) (hP : P.IsPrime), P = IsLocalRing.maximalIdeal ↥V →
      @ValuationSubring.ofPrime K _ V P hP = V := by
    rintro P hP rfl
    exact ValuationSubring.ofPrime_top V
  have h2 : V.ofPrime (V.idealOfLE W hVW) = W := ValuationSubring.ofPrime_idealOfLE V W hVW
  rw [key _ _ heq] at h2
  exact h2


-- created on 2026-10-05
