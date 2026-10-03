import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_map_maximalIdeal_le_jacobson_bot_of_isIntegral.lean)
-/
@[main]
private lemma main
  [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [Algebra.IsIntegral R S] :
-- imply
  (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≤ Ideal.jacobson (⊥ : Ideal S) := by
-- proof
  refine le_sInf fun M ⟨_, hM⟩ ↦ Ideal.map_le_iff_le_comap.mpr ?_
  have : M.IsMaximal := hM
  have : (M.comap (algebraMap R S)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  exact (eq_maximalIdeal this).ge


-- created on 2026-10-03
