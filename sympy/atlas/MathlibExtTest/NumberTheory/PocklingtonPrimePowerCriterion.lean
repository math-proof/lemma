/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PocklingtonPrimePowerCriterion.lean -/


import Lemma.Nat.PocklingtonPrimePowerCriterion
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Prime

-- The witness `a = 2` certifies `13 = 3 * 2 ^ 2 + 1`.
example : Nat.Prime 13 := by
  apply MetaMathlibExt.pocklington_prime_power_criterion 13 3 2 2
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine ⟨2, ?_, ?_⟩
    · norm_num
    · norm_num

-- The witness `a = 5` certifies `97 = 3 * 2 ^ 5 + 1`.
example : Nat.Prime 97 := by
  apply MetaMathlibExt.pocklington_prime_power_criterion 97 3 2 5
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · refine ⟨5, ?_, ?_⟩
    · norm_num
    · norm_num
