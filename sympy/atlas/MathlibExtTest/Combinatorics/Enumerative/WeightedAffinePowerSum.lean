/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/WeightedAffinePowerSum.lean -/


import Mathlib.Tactic.NormNum
import sympy.atlas.Combinatorics.Enumerative.WeightedAffinePowerSum

namespace MetaMathlibExt

example : weightedAffinePowerSum (R := ℤ) 1 0 1 3 1 = 6 := by
  norm_num [weightedAffinePowerSum, Finset.sum_range_succ]

example (a b : ℤ) (u : ℤ) : weightedAffinePowerSum a b u 0 0 = 1 := by
  simp [weightedAffinePowerSum]

end MetaMathlibExt
