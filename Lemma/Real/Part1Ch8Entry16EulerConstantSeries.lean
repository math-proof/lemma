import Mathlib
import sympy.Basic
import sympy.functions.special.ramanujan.Part1Ch8Entry16EulerConstantSeries

open Ramanujan.Part1Ch8.Entry16Eulerconstantseries

/--
[Part1Ch8Entry16EulerConstantSeries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry16EulerConstantSeries.lean)
-/
@[path]
private lemma ramanujan_part1_ch8_entry16_eulerconstantseries_eq :
-- imply
  Summable (fun k : ℕ =>
    ((k + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.Icc (((3 ^ k - 1) / 2 + 1 : ℕ)) (((3 ^ (k + 1) - 1) / 2 : ℕ)),
        (1 : ℝ) / ((3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ))) ∧
    Real.eulerMascheroniConstant =
      Real.log 2 - 2 * ∑' k : ℕ,
        ((k + 1 : ℕ) : ℝ) *
          ∑ j ∈ Finset.Icc (((3 ^ k - 1) / 2 + 1 : ℕ)) (((3 ^ (k + 1) - 1) / 2 : ℕ)),
            (1 : ℝ) / ((3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ)) := by
-- proof
  apply Ramanujan.Part1Ch8.Entry16Eulerconstantseries.ramanujan_part1_ch8_entry16_eulerconstantseries

-- created on 2026-10-10
