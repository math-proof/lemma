import Mathlib
import sympy.Basic


/--
[IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal.lean)
-/
@[main]
private lemma main
  [CommRing A] [IsLocalRing A]
  {p : ℕ} [Fact p.Prime]
-- given
  (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
-- imply
  CharP (IsLocalRing.ResidueField A) p := by
-- proof
  have h0 : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hAp
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h0


-- created on 2026-10-03
