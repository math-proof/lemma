import Mathlib
import sympy.Basic

open IsLocalRing

/--
[IsLocalRing_maximalIdeal_eq_of_le_sup_sq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_maximalIdeal_eq_of_le_sup_sq.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  {N : Ideal R}
-- given
  (hN : N ≤ maximalIdeal R)
  (h : maximalIdeal R ≤ N ⊔ maximalIdeal R ^ 2) :
-- imply
  maximalIdeal R = N := by
-- proof
  classical
  refine le_antisymm ?_ hN
  have hfg : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) (N := N) hfg ?_ ?_
  · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  · rw [Ideal.smul_eq_mul, ← pow_two]; exact h


-- created on 2026-10-05
