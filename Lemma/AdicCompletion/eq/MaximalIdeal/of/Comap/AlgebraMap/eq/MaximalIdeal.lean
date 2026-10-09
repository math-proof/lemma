import sympy.Basic
import Mathlib

open IsLocalRing

/--
[AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal.lean)
-/
@[path]
private lemma main
-- given
  (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime] (hP : Ideal.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) P = maximalIdeal R) :
-- imply
  P = maximalIdeal (AdicCompletion (maximalIdeal R) R) := by
-- proof
  refine ((IsLocalRing.maximalIdeal.isMaximal _).eq_of_le
    (Ideal.IsPrime.ne_top inferInstance) ?_).symm
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, hP]

-- created on 2026-10-09
