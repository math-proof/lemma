/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/GeneralizedStirlingNumbers.lean -/


import Def.Combinatorics.Enumerative.GeneralizedStirlingNumbers
import Lemma.Finset.Enumerative.GeneralizedStirlingNumbers
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

example : generalizedStirlingFirst 0 0 (0 : ℝ) = 1 := by
  have h1 : Nat.choose (0 + 0) 0 = 1 := by decide
  have h2 : Nat.stirlingFirst 0 (0 + 0) = 1 := by decide
  have hr : (0 - 0 + 1) = 1 := by decide
  simp only [generalizedStirlingFirst, hr, Finset.sum_range_one, h1, h2]
  ring

example : generalizedStirlingFirst 2 2 (2 : ℝ) = 1 := by
  have h1 : Nat.choose (0 + 2) 2 = 1 := by decide
  have h2 : Nat.stirlingFirst 2 (0 + 2) = 1 := by decide
  have hr : (2 - 2 + 1) = 1 := by decide
  simp only [generalizedStirlingFirst, hr, Finset.sum_range_one, h1, h2]
  ring

example : generalizedStirlingFirst 1 0 (0 : ℝ) = 0 := by
  have h1 : Nat.choose (0 + 0) 0 = 1 := by decide
  have h2 : Nat.stirlingFirst 1 (0 + 0) = 0 := by decide
  have h3 : Nat.choose (1 + 0) 0 = 1 := by decide
  have h4 : Nat.stirlingFirst 1 (1 + 0) = 1 := by decide
  have hr : (1 - 0 + 1) = 2 := by decide
  simp only [generalizedStirlingFirst, hr, Finset.sum_range_succ,
    Finset.sum_range_zero, h1, h2, h3, h4]
  ring

example : generalizedStirlingFirst 1 0 (2 : ℝ) = 2 := by
  have h1 : Nat.choose (0 + 0) 0 = 1 := by decide
  have h2 : Nat.stirlingFirst 1 (0 + 0) = 0 := by decide
  have h3 : Nat.choose (1 + 0) 0 = 1 := by decide
  have h4 : Nat.stirlingFirst 1 (1 + 0) = 1 := by decide
  have hr : (1 - 0 + 1) = 2 := by decide
  simp only [generalizedStirlingFirst, hr, Finset.sum_range_succ,
    Finset.sum_range_zero, h1, h2, h3, h4]
  ring

example : generalizedStirlingSecond 0 0 (0 : ℝ) = 1 := by
  have h1 : Nat.choose 0 0 = 1 := by decide
  have h2 : Nat.stirlingSecond (0 - 0) 0 = 1 := by decide
  have hr : (0 - 0 + 1) = 1 := by decide
  simp only [generalizedStirlingSecond, hr, Finset.sum_range_one, h1, h2]
  ring

example : generalizedStirlingSecond 2 2 (2 : ℝ) = 1 := by
  have h1 : Nat.choose 2 0 = 1 := by decide
  have h2 : Nat.stirlingSecond (2 - 0) 2 = 1 := by decide
  have hr : (2 - 2 + 1) = 1 := by decide
  simp only [generalizedStirlingSecond, hr, Finset.sum_range_one, h1, h2]
  ring

example : generalizedStirlingSecond 1 0 (0 : ℝ) = 0 := by
  have h1 : Nat.choose 1 0 = 1 := by decide
  have h2 : Nat.stirlingSecond (1 - 0) 0 = 0 := by decide
  have h3 : Nat.choose 1 1 = 1 := by decide
  have h4 : Nat.stirlingSecond (1 - 1) 0 = 1 := by decide
  have hr : (1 - 0 + 1) = 2 := by decide
  simp only [generalizedStirlingSecond, hr, Finset.sum_range_succ,
    Finset.sum_range_zero, h1, h2, h3, h4]
  ring

example : generalizedStirlingSecond 1 0 (2 : ℝ) = 2 := by
  have h1 : Nat.choose 1 0 = 1 := by decide
  have h2 : Nat.stirlingSecond (1 - 0) 0 = 0 := by decide
  have h3 : Nat.choose 1 1 = 1 := by decide
  have h4 : Nat.stirlingSecond (1 - 1) 0 = 1 := by decide
  have hr : (1 - 0 + 1) = 2 := by decide
  simp only [generalizedStirlingSecond, hr, Finset.sum_range_succ,
    Finset.sum_range_zero, h1, h2, h3, h4]
  ring

end MetaMathlibExt
