import Mathlib
import sympy.Basic


/--
[ValuationSubring_residue_eq_residue_iff_valuation_sub_lt_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_residue_eq_residue_iff_valuation_sub_lt_one.lean)
-/
@[main]
private lemma main
  [Field K]
  {A : ValuationSubring K}
  {a b : K}
-- given
  (ha : a ∈ A)
  (hb : b ∈ A) :
-- imply
  IsLocalRing.residue A ⟨a, ha⟩ = IsLocalRing.residue A ⟨b, hb⟩ ↔ A.valuation (a - b) < 1 := by
-- proof
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
  rfl


-- created on 2026-10-03
