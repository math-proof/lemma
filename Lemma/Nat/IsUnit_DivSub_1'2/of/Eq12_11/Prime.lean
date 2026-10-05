import Mathlib
import sympy.Basic


/--
[IsLocalRing_isUnit_natCast_guardPrime_sub_one_div_two_of_charP_two](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_isUnit_natCast_guardPrime_sub_one_div_two_of_charP_two.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsLocalRing R] [CharP (IsLocalRing.ResidueField R) 2]
  {ℓg : ℕ}
-- given
  (_hℓg : ℓg.Prime)
  (hℓg12 : ℓg % 12 = 11) :
-- imply
  IsUnit (((ℓg - 1) / 2 : ℕ) : R) := by
-- proof
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast]
  intro h
  have hd := (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R) 2 _).mp h
  omega


-- created on 2026-10-03
