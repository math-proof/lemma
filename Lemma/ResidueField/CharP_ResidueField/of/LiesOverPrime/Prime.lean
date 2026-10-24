import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Int.P2MUtil


/--
[ValuationSubring_residueField_charP_of_liesOverPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_residueField_charP_of_liesOverPrime.lean)
-/
@[path]
private lemma main
  [Field L]
  {A : ValuationSubring L}
  {ℓ : ℕ}
-- given
  (hℓ : ℓ.Prime)
  (hA : A.LiesOverPrime ℓ) :
-- imply
  CharP (IsLocalRing.ResidueField A) ℓ := by
-- proof
  refine (CharP.charP_iff_prime_eq_zero hℓ).mpr ?_
  rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  have : (((ℓ : ℕ) : A) : L) = (ℓ : L) := by simp
  rw [this]
  exact hA


-- created on 2026-10-23
