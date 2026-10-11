import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch8Entry14ViiIntegral8

open MeasureTheory
open Ramanujan.Part1Ch8.Entry14ViiIntegral8

/--
[Part1Ch8Entry14ViiIntegral8](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry14ViiIntegral8.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry14_vii_integral8_eq
-- given
  (x : ℝ)
  (hx : |x| < 1) :
-- imply
  IntervalIntegrable (fun u : ℝ => 1 / (1 + u ^ (8 : ℕ))) volume 0 x ∧
    0 <
      (1 + x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2) /
        (1 - x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2) ∧
    0 <
      (1 + x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2) /
        (1 - x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2) ∧
    1 - x ^ 2 ≠ 0 ∧
    chapter8Entry14A 8 x =
      Real.sqrt (2 + Real.sqrt 2) / 16 *
          (Real.log
              ((1 + x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2) /
                (1 - x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2)) +
            2 * Real.arctan
              (x * Real.sqrt (2 + Real.sqrt 2) / (1 - x ^ 2))) +
        Real.sqrt (2 - Real.sqrt 2) / 16 *
          (Real.log
              ((1 + x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2) /
                (1 - x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2)) +
            2 * Real.arctan
              (x * Real.sqrt (2 - Real.sqrt 2) / (1 - x ^ 2))) := by
-- proof
  apply Ramanujan.Part1Ch8.Entry14ViiIntegral8.ramanujan_part1_ch8_entry14_vii_integral8 x hx

-- created on 2026-10-10
