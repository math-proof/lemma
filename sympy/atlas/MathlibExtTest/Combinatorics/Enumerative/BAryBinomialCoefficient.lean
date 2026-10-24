/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/BAryBinomialCoefficient.lean -/


import sympy.atlas.Combinatorics.Enumerative.BAryBinomialCoefficient
import Lemma.Finset.Enumerative.BAryBinomialCoefficient

namespace MetaMathlibExt

example : bAryBinomialCoefficient 2 0 0 (by decide) = 1 := by decide
example : bAryBinomialCoefficient 2 5 1 (by decide) = 1 := by decide
example : bAryBinomialCoefficient 2 5 2 (by decide) = 0 := by decide
example : bAryBinomialCoefficient 3 8 4 (by decide) = 4 := by decide
example : bAryBinomialCoefficient 3 8 9 (by decide) = 0 := by decide

example : bAryBinomialCoefficient 3 8 4 (by decide) =
    ∏ i ∈ Finset.range 5, ((Nat.digits 3 8).getD i 0).choose ((Nat.digits 3 4).getD i 0) :=
  bAryBinomialCoefficient_eq_prod_getD 3 8 4 (by decide) (by decide) (by decide)

example : bAryBinomialCoefficient 3 8 4 (by decide) = 4 := by
  rw [bAryBinomialCoefficient_eq_prod_getD 3 8 4 (by decide) (L := 5) (by decide) (by decide)]
  decide

example : bAryBinomialCoefficient 3 8 9 (by decide) = 0 := by
  rw [bAryBinomialCoefficient_eq_prod_getD 3 8 9 (by decide) (L := 4) (by decide) (by decide)]
  decide

end MetaMathlibExt
