/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Ramanujan/Part1Ch3Entry13CorollarySchroder.lean -/


import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Def.NumberTheory.Ramanujan.Part1Ch3Entry13CorollarySchroder
import Lemma.Nat.Ramanujan.Part1Ch3Entry13CorollarySchroder
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry13CorollarySchroder


-- At `w = 0`, the theorem recovers the ordinary exponential series at `z = 2`.
example : HasSum (fun k : ℕ => (2 : ℂ) ^ k / (Nat.factorial k : ℂ)) (Complex.exp 2) := by
  have h := ramanujan_part1_ch3_entry13_corollary_schroder (2 : ℂ) 0 (by simp) (by norm_num)
  refine h.congr_fun (fun k => ?_)
  cases k with
  | zero => simp
  | succ n =>
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.cast_add, Nat.cast_one, mul_zero,
        add_zero, Complex.exp_zero, mul_one, Nat.add_sub_cancel]
      rw [pow_succ]
      ring

-- At degree two, the public Abel identity agrees with its direct ring expansion.
example (w x y : ℂ) :
    x * (x + 2 * w) + 2 * x * y + y * (y + 2 * w) =
      (x + y) * (x + y + 2 * w) := by
  have h := schroder_abel_binomial w x y 2
  norm_num [Finset.sum_range_succ] at h
  linear_combination h

