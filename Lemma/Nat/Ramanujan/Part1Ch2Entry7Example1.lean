import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry7Example1
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry7Example1


/--
[ramanujan_part1_ch2_entry7_example1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Example1.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry7_example1_eq
  {n : ℝ}
-- given
  (hn_pos : 0 < n)
  (hn_ne : n ≠ (Real.sqrt 5 - 1) / 2) :
-- imply
  HasSum (fun k : ℕ => Real.arctan (2 / ((n + (k : ℝ) + 1) ^ 2)))
    (Real.arctan ((2 * n + 1) / (n ^ 2 + n - 1)) + if n < (Real.sqrt 5 - 1) / 2 then Real.pi else
    0) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Example1.ramanujan_part1_ch2_entry7_example1 n hn_pos hn_ne


-- created on 2026-10-20
