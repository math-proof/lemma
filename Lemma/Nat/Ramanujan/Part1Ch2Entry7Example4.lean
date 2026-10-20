import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry7Example4
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry7Example4


/--
[ramanujan_part1_ch2_entry7_example4](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example4.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry7_example4_eq
  :
-- imply
  HasSum (fun k : ℕ => Real.arctan (2 / (((k : ℝ) + 1) ^ 2))) (3 * Real.pi / 4) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example4.ramanujan_part1_ch2_entry7_example4


-- created on 2026-10-20
