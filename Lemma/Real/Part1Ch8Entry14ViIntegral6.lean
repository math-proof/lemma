import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch8Entry14ViIntegral6

open MeasureTheory
open Ramanujan.Part1Ch8.Entry14ViIntegral6

/--
[Part1Ch8Entry14ViIntegral6](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry14ViIntegral6.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry14_vi_integral6_eq
-- given
  (x : ℝ) :
-- imply
  IntervalIntegrable (fun u : ℝ => 1 / (1 + u ^ (6 : ℕ))) volume 0 x ∧
    0 < 1 + x * Real.sqrt 3 + x ^ 2 ∧
    0 < 1 - x * Real.sqrt 3 + x ^ 2 ∧
    chapter8Entry14A 6 x =
      (1 / 2 : ℝ) * Real.arctan x +
        (1 / 6 : ℝ) * Real.arctan (x ^ 3) +
        1 / (4 * Real.sqrt 3) *
          Real.log
            ((1 + x * Real.sqrt 3 + x ^ 2) /
              (1 - x * Real.sqrt 3 + x ^ 2)) := by
-- proof
  apply Ramanujan.Part1Ch8.Entry14ViIntegral6.ramanujan_part1_ch8_entry14_vi_integral6 x

-- created on 2026-10-10
