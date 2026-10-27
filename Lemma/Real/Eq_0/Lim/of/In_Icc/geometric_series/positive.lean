import Mathlib.Analysis.SpecificLimits.Basic
import Def.Analysis.Real.Limits.Part4
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
open Topology


/--
For `0 < x < 1`, the geometric powers tend to zero: `lim [n → ∞] x ^ n = 0`.
-/
@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Ioo (0 : ℝ) 1) :
-- imply
  lim [n → ∞] x ^ n = 0 := by
-- proof
  simpa using tendsto_pow_atTop_nhds_zero_of_lt_one h.1.le h.2


-- created on 2023-04-16
