import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch8Entry14VIntegral5

open MeasureTheory
open Ramanujan.Part1Ch8.Entry14VIntegral5

/--
[Part1Ch8Entry14VIntegral5](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry14VIntegral5.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry14_v_integral5_eq
-- given
  (x : ℝ)
  (hxLower : -1 < x)
  (hxUpper : x < 4 / (Real.sqrt 5 + 1)) :
-- imply
  IntervalIntegrable (fun u : ℝ => 1 / (1 + u ^ (5 : ℕ))) volume 0 x ∧
    0 < (1 + x) ^ 5 / (1 + x ^ 5) ∧
    0 <
      (1 + (1 / 2 : ℝ) * x * (Real.sqrt 5 - 1) + x ^ 2) /
        (1 - (1 / 2 : ℝ) * x * (Real.sqrt 5 + 1) + x ^ 2) ∧
    4 + x * (Real.sqrt 5 - 1) ≠ 0 ∧
    4 - x * (Real.sqrt 5 + 1) ≠ 0 ∧
    chapter8Entry14A 5 x =
      (1 / 20 : ℝ) * Real.log ((1 + x) ^ 5 / (1 + x ^ 5)) +
        1 / (4 * Real.sqrt 5) *
          Real.log
            ((1 + (1 / 2 : ℝ) * x * (Real.sqrt 5 - 1) + x ^ 2) /
              (1 - (1 / 2 : ℝ) * x * (Real.sqrt 5 + 1) + x ^ 2)) +
        (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
          Real.arctan
            (x * Real.sqrt (10 + 2 * Real.sqrt 5) /
              (4 + x * (Real.sqrt 5 - 1))) +
        (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
          Real.arctan
            (x * Real.sqrt (10 - 2 * Real.sqrt 5) /
              (4 - x * (Real.sqrt 5 + 1))) := by
-- proof
  apply Ramanujan.Part1Ch8.Entry14VIntegral5.ramanujan_part1_ch8_entry14_v_integral5 x hxLower hxUpper

-- created on 2026-10-10
