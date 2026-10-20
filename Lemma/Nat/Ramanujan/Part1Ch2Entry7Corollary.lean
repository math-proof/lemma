import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry7Corollary
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry7Corollary


/--
[ramanujan_part1_ch2_entry7_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry7Corollary.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry7_corollary_eq
  {n : ℝ}
-- given
  (hn : 0 < n) :
-- imply
  HasSum (fun k : ℕ => Real.arctan (2 / ((n + 2 * (k : ℝ) + 1) ^ 2))) (Real.arctan (1 / n)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry7Corollary.ramanujan_part1_ch2_entry7_corollary n hn


-- created on 2026-10-20
