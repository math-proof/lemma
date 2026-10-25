/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/RParameterGeneralizedFibonacciSequence.lean -/


import Mathlib.Tactic
import Def.Combinatorics.Enumerative.RParameterGeneralizedFibonacciSequence


namespace MetaMathlibExt

example (r : ℝ) : rFibonacciNumber r 0 = 1 := by
  simp [rFibonacciNumber]

example (r : ℝ) : rFibonacciNumber r 3 = 1 + 2 * r := by
  simp [rFibonacciNumber, Finset.sum_range_succ]

end MetaMathlibExt
