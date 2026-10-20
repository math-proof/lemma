import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry7Example6
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry7Example6


/--
[ramanujan_part1_ch2_entry7_example6](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example6.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry7_example6_eq
  :
-- imply
  HasSum (fun k : ℕ => Real.arctan (1 / ((1 + Real.sqrt 2 * (↑(k + 1) : ℝ)) ^ 2)))
    (Real.pi / 8) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example6.ramanujan_part1_ch2_entry7_example6


-- created on 2026-10-20
