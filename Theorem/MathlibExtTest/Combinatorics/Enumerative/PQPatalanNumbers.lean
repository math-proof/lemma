/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/PQPatalanNumbers.lean -/
module

public import Mathlib.Tactic.NormNum
public import Def.Combinatorics.Enumerative.PQPatalanNumbers.Part2
public import Def.MathlibExtTest.Combinatorics.Enumerative.PQPatalanNumbers

public section

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
