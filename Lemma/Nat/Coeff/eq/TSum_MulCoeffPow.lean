import Mathlib
import sympy.Basic

open PowerSeries

/--
[PowerSeries_coeff_zero_taylorShift](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PowerSeries_coeff_zero_taylorShift.lean)
-/
@[path]
private lemma main
  [NontriviallyNormedField L] [CompleteSpace L] [IsUltrametricDist L]
  {F : PowerSeries L}
  {a : L} :
-- imply
  PowerSeries.coeff 0 (PowerSeries.mk fun n => ∑' k : ℕ,
        PowerSeries.coeff (n + k) F * ((n + k).choose n : L) * a ^ k)
      = ∑' k, PowerSeries.coeff k F * a ^ k := by
-- proof
  rw [PowerSeries.coeff_mk]
  refine tsum_congr fun k => ?_
  simp


-- created on 2026-10-05
