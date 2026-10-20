import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry7Example5Alternating
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry7Example5Alternating


/--
[ramanujan_part1_ch2_entry7_example5_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5Alternating.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry7_example5_alternating_eq
  :
-- imply
  HasSum (fun n : ℕ => (-1 : ℝ) ^ n * Real.arctan ((2 : ℝ) / (((n : ℝ) + 1) ^ 2))) (Real.pi / 4) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5Alternating.ramanujan_part1_ch2_entry7_example5_alternating


-- created on 2026-10-20
