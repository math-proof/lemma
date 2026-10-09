import Mathlib
import sympy.Basic


/--
[ValuationSubring_residue_ne_zero_iff_valuation_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_residue_ne_zero_iff_valuation_eq_one.lean)
-/
@[path]
private lemma main
  [Field K]
  {A : ValuationSubring K}
  {a : K}
-- given
  (ha : a ∈ A) :
-- imply
  IsLocalRing.residue A ⟨a, ha⟩ ≠ 0 ↔ A.valuation a = 1 := by
-- proof
  rw [IsLocalRing.residue_ne_zero_iff_isUnit, A.valuation_eq_one_iff]


-- created on 2026-10-03
