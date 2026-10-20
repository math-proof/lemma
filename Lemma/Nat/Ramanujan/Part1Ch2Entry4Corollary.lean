import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch2Entry4Corollary
open MathlibExt.NumberTheory.Ramanujan.Part1Ch2
open Entry4Corollary


/--
[ramanujan_part1_ch2_entry4_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch2Entry4Corollary.lean)
-/
@[path]
private lemma ramanujan_part1_ch2_entry4_corollary_eq
  :
-- imply
  HasSum (fun j : ℕ => (2 : ℝ) / ((4 * ((j : ℝ) + 1)) ^ 3 - 4 * ((j : ℝ) + 1)))
    ((3 : ℝ) / 2 * Real.log 2 - 1) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch2.Entry4Corollary.ramanujan_part1_ch2_entry4_corollary


-- created on 2026-10-20
