import Mathlib.Analysis.SpecificLimits.Basic
import Def.Analysis.Real.Limits.Basic
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
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
-- updated on 2026-10-26
