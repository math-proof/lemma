import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry7Example5First
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry7Example5First


/--
[ramanujan_part1_ch2_entry7_example5_first](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example5First.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry7_example5_first_eq
  :
-- imply
  HasSum (fun n : ℕ => Real.arctan (1 / (2 * ((n + 1 : ℕ) : ℝ) ^ 2))) (Real.pi / 4) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example5First.ramanujan_part1_ch2_entry7_example5_first


-- created on 2026-10-20
