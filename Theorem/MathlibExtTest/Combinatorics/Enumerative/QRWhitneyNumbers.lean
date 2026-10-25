/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/QRWhitneyNumbers.lean -/


import Def.Combinatorics.Enumerative.QRWhitneyNumbers
import Lemma.Finset.Enumerative.QRWhitneyNumbers
import Mathlib.Tactic.NormNum


namespace MetaMathlibExt.QRWhitney

example : qBrack (3 : ℂ) 3 = 13 := by
  norm_num [qBrack, Finset.sum_range_succ]

example (m r q : ℂ) : whitneySecond m r q 1 1 = 1 := by
  simp [whitneySecond, qBrack]

example (m r q : ℂ) [NeZero q] : whitneyFirst m r q 2 3 = 0 :=
  whitneyFirst_eq_zero_of_lt (by omega)

example : whitneyFirst 2 3 1 2 0 = 15 := by
  norm_num [whitneyFirst, qBrack, Finset.sum_range_succ]

example : whitneySecond 2 3 1 2 1 = 8 := by
  norm_num [whitneySecond, qBrack, Finset.sum_range_succ]

end MetaMathlibExt.QRWhitney
