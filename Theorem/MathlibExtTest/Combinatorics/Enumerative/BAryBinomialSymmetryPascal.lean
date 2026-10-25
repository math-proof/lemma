/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/BAryBinomialSymmetryPascal.lean -/


import Lemma.Finset.Enumerative.BAryBinomialSymmetryPascal


namespace MetaMathlibExt

-- Positions past the last digit of `8 = 22₃` and `4 = 11₃` contribute `choose 0 0 = 1`.
example : bAryBinomialCoefficient 3 8 4 (by decide) = 4 := by
  rw [bAryBinomialCoefficient_eq_prod_div_pow 3 8 4 (by decide) (L := 4) (by decide) (by decide)]
  decide

example : bAryBinomialCoefficient 3 6 3 (by decide) = 2 := by
  rw [bAryBinomialCoefficient_eq_prod_div_pow 3 6 3 (by decide) (L := 2) (by decide) (by decide)]
  decide

example : bAryBinomialCoefficient 3 8 9 (by decide) = 0 := by
  rw [bAryBinomialCoefficient_eq_prod_div_pow 3 8 9 (by decide) (L := 3) (by decide) (by decide)]
  decide

example : bAryBinomialCoefficient 3 8 2 (by decide) = bAryBinomialCoefficient 3 8 6 (by decide) :=
  bAryBinomialCoefficient_symm 3 8 2 (by decide) (by decide)

example : bAryBinomialCoefficient 2 5 2 (by decide) = bAryBinomialCoefficient 2 5 3 (by decide) :=
  bAryBinomialCoefficient_symm 2 5 2 (by decide) (by decide)

example (n : ℕ) :
    bAryBinomialCoefficient 3 n 0 (by decide) = bAryBinomialCoefficient 3 n n (by decide) :=
  bAryBinomialCoefficient_symm 3 n 0 (by decide) n.zero_le

example : bAryBinomialCoefficient 3 8 4 (by decide) =
    bAryBinomialCoefficient 3 7 3 (by decide) + bAryBinomialCoefficient 3 7 4 (by decide) :=
  bAryBinomialCoefficient_pascal 3 8 4 (by decide) (by decide) (by decide) (by decide)

-- `6 = 20₃` has a trailing zero digit, so `n - 1 = 12₃` borrows.
example : bAryBinomialCoefficient 3 6 3 (by decide) =
    bAryBinomialCoefficient 3 5 2 (by decide) + bAryBinomialCoefficient 3 5 3 (by decide) :=
  bAryBinomialCoefficient_pascal 3 6 3 (by decide) (by decide) (by decide) (by decide)

example : bAryBinomialCoefficient 2 4 4 (by decide) =
    bAryBinomialCoefficient 2 3 3 (by decide) + bAryBinomialCoefficient 2 3 4 (by decide) :=
  bAryBinomialCoefficient_pascal 2 4 4 (by decide) (by decide) (by decide) (by decide)

-- The recurrence needs a nonzero coefficient: `bAryBinomialCoefficient 2 2 1 = 0`, but `1 + 1`.
example : bAryBinomialCoefficient 2 2 1 (by decide) ≠
    bAryBinomialCoefficient 2 1 0 (by decide) + bAryBinomialCoefficient 2 1 1 (by decide) := by
  decide

end MetaMathlibExt
