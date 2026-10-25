/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PQPatalanNumbers.lean -/


import Mathlib.Tactic.NormNum
import Def.Combinatorics.Enumerative.PQPatalanNumbers.Part2
import Def.MathlibExtTest.Combinatorics.Enumerative.PQPatalanNumbers


namespace MetaMathlibExt

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
