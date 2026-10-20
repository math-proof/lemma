import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry7Example2
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry7Example2


/--
[ramanujan_part1_ch2_entry7_example2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example2.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry7_example2_eq
  {n : ℝ}
-- given
  (hn : 0 < n) :
-- imply
  HasSum (fun k : ℕ => (-1 : ℝ) ^ k * Real.arctan (2 / (n + (k : ℝ) + 1) ^ 2))
    (Real.arctan (1 / (n ^ 2 + n + 1))) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example2.ramanujan_part1_ch2_entry7_example2 n hn


-- created on 2026-10-20
