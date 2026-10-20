import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry2Corollary
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry2Corollary


/--
[ramanujan_part1_ch2_entry2_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry2Corollary.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry2_corollary_eq
  :
-- imply
  HasSum (fun j : ℕ => (1 : ℝ) / ((3 * ((j : ℝ) + 1)) ^ 3 - 3 * ((j : ℝ) + 1)))
    ((Real.log 3 - 1) / 2) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry2Corollary.ramanujan_part1_ch2_entry2_corollary


-- created on 2026-10-20
