/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PQPatalanNumbers.lean -/


import Mathlib.Tactic.NormNum
import sympy.atlas.Combinatorics.Enumerative.PQPatalanNumbers

namespace MetaMathlibExt

private def catalanPatalanParams : PQPatalanParams where
  p := 2
  q := 1
  hp := by decide
  hq_pos := by decide
  hq := by decide

example : pqPatalanNumber catalanPatalanParams 0 = 1 := by
  norm_num [pqPatalanNumber, patalanGeneralizedBinomial, catalanPatalanParams,
    Finset.prod_range_succ, Nat.factorial]

example : pqPatalanNumber catalanPatalanParams 1 = 1 := by
  norm_num [pqPatalanNumber, patalanGeneralizedBinomial, catalanPatalanParams,
    Finset.prod_range_succ, Nat.factorial]

example : pqPatalanNumber catalanPatalanParams 2 = 2 := by
  norm_num [pqPatalanNumber, patalanGeneralizedBinomial, catalanPatalanParams,
    Finset.prod_range_succ, Nat.factorial]

end MetaMathlibExt
