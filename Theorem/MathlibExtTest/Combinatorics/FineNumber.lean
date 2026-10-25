/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FineNumber.lean -/


import Def.Combinatorics.FineNumber
import Lemma.Finset.FineNumber
import Mathlib.Tactic
open MetaMathlibExt


example (n : Nat) :
    fineNumber n = (1 / ((n : ℚ) + 1)) * ∑ i ∈ Finset.range (n + 1),
      (-2 : ℚ) ^ i * ((i : ℚ) + 1) * ((Nat.choose (2 * (n + 1)) (n - i) : ℕ) : ℚ) :=
  rfl

example (n : Nat) :
    fineNumber n = (1 / ((n : ℚ) + 1)) * ∑ i ∈ Finset.range (n + 1),
      (-2 : ℚ) ^ i * ((i : ℚ) + 1) * ((Nat.choose (2 * (n + 1)) (n - i) : ℕ) : ℚ) :=
  fineNumber_eq_sum n

example :
    (-2 : ℚ) ^ (0 : Nat) * (((0 : Nat) : ℚ) + 1) *
      ((Nat.choose (2 * (2 + 1)) (2 - 0) : ℕ) : ℚ) = 15 := by norm_num [Nat.choose]

example :
    (-2 : ℚ) ^ (2 : Nat) * (((2 : Nat) : ℚ) + 1) *
      ((Nat.choose (2 * (2 + 1)) (2 - 2) : ℕ) : ℚ) = 12 := by norm_num [Nat.choose]

example : fineNumber 0 = 1 := by
  norm_num [fineNumber, Finset.sum_range_succ, Nat.choose]

example : fineNumber 1 = 0 := by
  norm_num [fineNumber, Finset.sum_range_succ, Nat.choose]

example : fineNumber 2 = 1 := by
  norm_num [fineNumber, Finset.sum_range_succ, Nat.choose]

