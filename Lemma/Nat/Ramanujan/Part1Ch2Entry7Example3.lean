import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry7Example3
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry7Example3


/--
[ramanujan_part1_ch2_entry7_example3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example3.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry7_example3_eq
  {n : ℝ}
-- given
  (hn : 0 < n) :
-- imply
  HasSum (fun k : ℕ => Real.arctan (1 / (2 * (n + (k : ℝ) + 1) ^ 2)))
    (Real.arctan (1 / (2 * n + 1))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example3.ramanujan_part1_ch2_entry7_example3 n hn


-- created on 2026-10-20
