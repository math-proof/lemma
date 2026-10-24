/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/FubiniRecurrence.lean -/


import Lemma.Finset.Enumerative.FubiniRecurrence

namespace MetaMathlibExt

example : (fubiniNumber 3 : ℤ) =
    (Nat.factorial 3 : ℤ) -
      ∑ j ∈ Finset.Icc 1 3, signedStirlingFirst 3 (3 - j) * (fubiniNumber (3 - j) : ℤ) :=
  fubiniNumber_eq_factorial_sub_sum_signed_stirling 3

end MetaMathlibExt
