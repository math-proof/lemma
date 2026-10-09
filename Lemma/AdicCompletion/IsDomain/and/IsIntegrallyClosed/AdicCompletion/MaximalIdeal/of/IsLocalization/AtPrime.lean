import sympy.Basic
import sympy.Flt
import Mathlib

open IsLocalRing

/--
[AdicCompletion_isDomain_and_isIntegrallyClosed_adicCompletion_maximalIdeal_of_isLocalization_atPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_isDomain_and_isIntegrallyClosed_adicCompletion_maximalIdeal_of_isLocalization_atPrime.lean)
-/
@[path]
private lemma main
  [CommRing O] [IsLocalRing O] [CommRing C] [Algebra O C]
  [CommRing S] [IsLocalRing S] [Algebra C S]
  {𝔫 : Ideal C} [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)] [IsLocalization.AtPrime S 𝔫]
-- given
  (hd : IsDomain (AdicCompletion 𝔫 C)) (hn : IsIntegrallyClosed (AdicCompletion 𝔫 C)) :
-- imply
  IsDomain (AdicCompletion (maximalIdeal S) S) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal S) S) := by
-- proof
  let e := BDescN6.adicEquiv 𝔫 S
  have := hd; have := hn
  refine ⟨MulEquiv.isDomain (AdicCompletion 𝔫 C) e.symm.toMulEquiv, ?_⟩
  apply IsIntegrallyClosed.of_equiv e

-- created on 2026-10-09
