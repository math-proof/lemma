/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean -/


import sympy.atlas.Combinatorics.Enumerative.LegendreStirlingFirstKind
import Lemma.Finset.Enumerative.LegendreStirlingFirstKind
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : legendreStirlingFirst 0 0 = 1 := by
  norm_num [legendreStirlingFirst_zero]

example : legendreStirlingFirst 3 4 = 0 :=
  legendreStirlingFirst_eq_zero_of_lt 3 4 (by decide)

example : legendreStirlingFirst 4 4 = 1 :=
  legendreStirlingFirst_diag 4

example : legendreStirlingFirst 3 1 = 12 := by
  rw [legendreStirlingFirst_succ 2 0, legendreStirlingFirst_two_zero,
    legendreStirlingFirst_two_one]
  norm_num

example : legendreStirlingFirst 3 2 = -8 := by
  rw [legendreStirlingFirst_succ 2 1, legendreStirlingFirst_two_one,
    legendreStirlingFirst_diag]
  norm_num

end MetaMathlibExt
