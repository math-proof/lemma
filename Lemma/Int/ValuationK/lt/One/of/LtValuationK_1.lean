import Mathlib
import sympy.Basic


/--
[ValuationSubring_valuation_intCast_lt_one_of_dvd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_valuation_intCast_lt_one_of_dvd.lean)
-/
@[path]
private lemma main
  [Field K]
  {A : ValuationSubring K}
  {q : ℕ}
  {a : ℤ}
-- given
  (hA : A.valuation (q : K) < 1)
  (hqa : (q : ℤ) ∣ a) :
-- imply
  A.valuation (a : K) < 1 := by
-- proof
  obtain ⟨b, rfl⟩ := hqa
  rw [Int.cast_mul, Int.cast_natCast, map_mul]
  calc A.valuation (q : K) * A.valuation (b : K)
      ≤ A.valuation (q : K) * 1 :=
        mul_le_mul' le_rfl ((A.valuation_le_one_iff _).mpr (intCast_mem A b))
    _ = A.valuation (q : K) := mul_one _
    _ < 1 := hA


-- created on 2026-10-03
