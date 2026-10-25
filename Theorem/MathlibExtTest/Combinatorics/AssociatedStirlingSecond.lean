/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/AssociatedStirlingSecond.lean -/


import Def.Combinatorics.AssociatedStirlingSecond
import Lemma.Finset.AssociatedStirlingSecond


namespace MetaMathlibExt

example : twoAssocStirlingSecond 0 0 = 1 := by decide

example : twoAssocStirlingSecond 6 3 = 15 := by decide

example : twoAssocStirlingSecond 6 4 = 0 :=
  twoAssocStirlingSecond_eq_zero_of_lt_two_mul 6 4 (by decide)

example :
    twoAssocStirlingSecond 6 3 =
      (3 : ℤ) * twoAssocStirlingSecond 5 3 +
        (5 : ℤ) * twoAssocStirlingSecond 4 2 :=
  twoAssocStirlingSecond_recurrence 4 3 (by decide) (by decide)

end MetaMathlibExt
