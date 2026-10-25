/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/StaverReciprocalBinomialSum.lean -/


import Lemma.Finset.StaverReciprocalBinomialSum
import Mathlib.Tactic.NormNum
open MetaMathlibExt


/-- Generic API: the promoted theorem fires at every `n` with the exact
Wanted statement shape. -/
example (n : Nat) :
    (Finset.range (n + 1)).sum (fun k => ((Nat.choose n k : Rat))⁻¹) =
      ((n + 1 : Rat) / (2 : Rat) ^ (n + 1)) *
        (Finset.Icc 1 (n + 1)).sum (fun k => (2 : Rat) ^ k / (k : Rat)) :=
  staver_reciprocal_binomial_sum n

example := staver_reciprocal_binomial_sum 0

example := staver_reciprocal_binomial_sum 1

example := staver_reciprocal_binomial_sum 2

example := staver_reciprocal_binomial_sum 3

-- Closed forms of the reciprocal-binomial side, including `n = 0`.
example : (Finset.range (0 + 1)).sum
    (fun k => ((Nat.choose 0 k : Rat))⁻¹) = 1 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

example : (Finset.range (1 + 1)).sum
    (fun k => ((Nat.choose 1 k : Rat))⁻¹) = 2 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

example : (Finset.range (2 + 1)).sum
    (fun k => ((Nat.choose 2 k : Rat))⁻¹) = 5 / 2 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

example : (Finset.range (3 + 1)).sum
    (fun k => ((Nat.choose 3 k : Rat))⁻¹) = 8 / 3 := by
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

-- Matching closed forms of the weighted power-sum side, each mediated by the
-- main theorem so the test exercises the promoted API rather than duplicating
-- the `Icc` recurrence.
example : ((0 + 1 : Rat) / (2 : Rat) ^ (0 + 1 : Nat)) *
    (Finset.Icc 1 (0 + 1 : Nat)).sum
      (fun k => (2 : Rat) ^ k / (k : Rat)) = 1 := by
  have h := staver_reciprocal_binomial_sum 0
  simp only [Nat.cast_zero] at h
  rw [← h]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

example : ((1 + 1 : Rat) / (2 : Rat) ^ (1 + 1 : Nat)) *
    (Finset.Icc 1 (1 + 1 : Nat)).sum
      (fun k => (2 : Rat) ^ k / (k : Rat)) = 2 := by
  have h := staver_reciprocal_binomial_sum 1
  simp only [Nat.cast_one] at h
  rw [← h]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

example : ((2 + 1 : Rat) / (2 : Rat) ^ (2 + 1 : Nat)) *
    (Finset.Icc 1 (2 + 1 : Nat)).sum
      (fun k => (2 : Rat) ^ k / (k : Rat)) = 5 / 2 := by
  have h := staver_reciprocal_binomial_sum 2
  simp only [Nat.cast_ofNat] at h
  rw [← h]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

example : ((3 + 1 : Rat) / (2 : Rat) ^ (3 + 1 : Nat)) *
    (Finset.Icc 1 (3 + 1 : Nat)).sum
      (fun k => (2 : Rat) ^ k / (k : Rat)) = 8 / 3 := by
  have h := staver_reciprocal_binomial_sum 3
  simp only [Nat.cast_ofNat] at h
  rw [← h]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero]

