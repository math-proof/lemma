import Mathlib
import sympy.Basic


/--
[HenselianLocalRing_of_isAdicComplete_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HenselianLocalRing_of_isAdicComplete_maximalIdeal.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] :
-- imply
  HenselianLocalRing R := by
-- proof
  refine { is_henselian := fun f hf a₀ h₁ h₂ => ?_ }
  exact HenselianRing.is_henselian f hf a₀ h₁ (h₂.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))


-- created on 2026-10-03
