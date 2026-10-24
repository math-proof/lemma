/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ClassicalLteTest.lean -/


import Lemma.Nat.ClassicalLte
import Mathlib.Tactic

namespace MetaMathlibExt

example :
    padicValInt 3 ((4 : ℤ) ^ 2 - 1 ^ 2) =
      padicValNat 3 2 + padicValInt 3 ((4 : ℤ) - 1) := by
  apply padicValInt_pow_sub_pow
  · decide
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end MetaMathlibExt
