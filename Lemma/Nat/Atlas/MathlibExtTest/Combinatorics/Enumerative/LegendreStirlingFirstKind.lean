import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.Enumerative.LegendreStirlingFirstKind


namespace MetaMathlibExt

/--
[legendreStirlingFirst_two_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean)
-/
@[path]
private lemma legendreStirlingFirst_two_zero : legendreStirlingFirst 2 0 = 0 := by
  norm_num [legendreStirlingFirst, jacobiStirlingFirst, jacobiStirlingFirstPoly,
    Finset.prod_range_succ, Polynomial.coeff_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[legendreStirlingFirst_two_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/LegendreStirlingFirstKind.lean)
-/
@[path]
private lemma legendreStirlingFirst_two_one : legendreStirlingFirst 2 1 = -2 := by
  rw [legendreStirlingFirst_succ 1 0]
  have h10 : legendreStirlingFirst 1 0 = 0 := by
    norm_num [legendreStirlingFirst, jacobiStirlingFirst, jacobiStirlingFirstPoly,
      Finset.prod_range_succ, Polynomial.coeff_mul]
  rw [h10, legendreStirlingFirst_diag]
  norm_num

end MetaMathlibExt


-- created on 2026-10-23
