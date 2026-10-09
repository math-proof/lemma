import Mathlib.Analysis.SpecificLimits.Basic
import sympy.series.limits
import sympy.sets.sets
import sympy.Basic
open Topology


/--
For `|x| < 1`, the geometric powers tend to zero: `lim [n → ∞] x ^ n = 0`.
-/
@[path]
private lemma main
  {x : ℝ}
-- given
  (h : |x| < 1) :
-- imply
  lim [n → ∞] x ^ n = 0 := by
-- proof
  simpa using tendsto_pow_atTop_nhds_zero_iff.mpr h


-- created on 2023-04-15
-- updated on 2023-05-20
