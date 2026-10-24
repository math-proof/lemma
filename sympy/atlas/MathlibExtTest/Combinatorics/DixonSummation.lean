/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/DixonSummation.lean -/


import sympy.atlas.Combinatorics.DixonSummation
import Lemma.Finset.DixonSummation

namespace MetaMathlibExt

-- Dixon's formula evaluates three representative positive terminating sums.
example :
    upsilon₃ 1 1 1 = 6 ∧ upsilon₃ 2 1 1 = 16 ∧ upsilon₃ 2 2 2 = 90 := by
  have ef2 : extFact (2 : ℤ) = 2 := by
    simpa [Nat.factorial] using (extFact_natCast 2)
  have ef3 : extFact (3 : ℤ) = 6 := by
    simpa [Nat.factorial] using (extFact_natCast 3)
  have ef4 : extFact (4 : ℤ) = 24 := by
    simpa [Nat.factorial] using (extFact_natCast 4)
  have ef6 : extFact (6 : ℤ) = 720 := by
    simpa [Nat.factorial] using (extFact_natCast 6)
  have if1 : invFact (1 : ℤ) = 1 := by
    simpa [Nat.factorial] using (invFact_natCast 1)
  have if2 : invFact (2 : ℤ) = 1 / 2 := by
    simpa [Nat.factorial] using (invFact_natCast 2)
  have if3 : invFact (3 : ℤ) = 1 / 6 := by
    simpa [Nat.factorial] using (invFact_natCast 3)
  have if4 : invFact (4 : ℤ) = 1 / 24 := by
    simpa [Nat.factorial] using (invFact_natCast 4)
  constructor
  · rw [dixon_summation]
    norm_num
    rw [ef2, ef3, if1, if2]
    norm_num
  · constructor
    · rw [dixon_summation]
      norm_num
      rw [ef2, ef4, if1, if2, if3]
      norm_num
    · rw [dixon_summation]
      norm_num
      rw [ef4, ef6, if2, if4]
      norm_num

example : intBinom 6 2 = 15 := by
  simpa [Nat.choose] using (intBinom_natCast (n := 6) (k := 2) (by norm_num))

example : intBinom 3 5 = 0 := by
  exact intBinom_of_lt (by norm_num)

example : intBinom 4 (-1) = 0 := by
  exact intBinom_of_neg_right (by norm_num)

-- The negative zero convention agrees with the universal inverse-factorial shift.
example : upsilon₃ (-1) 2 3 = 0 ∧ invFact (-2) = ((-2 : ℤ) + 1) * invFact (-1) := by
  constructor
  · rw [dixon_summation]
    norm_num [extFact_of_neg]
  · exact invFact_shift (-2)

end MetaMathlibExt
